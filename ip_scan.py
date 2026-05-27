import argparse
import ipaddress
import json
import os
import queue
import re
import secrets
import ssl
import shutil
import socket
import struct
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, asdict
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Callable, Dict, Iterable, List, Optional, Set, Tuple


@dataclass(frozen=True)
class GeoResult:
    ip: str
    input: str
    lat: float
    lon: float
    country: str = ""
    region: str = ""
    city: str = ""
    isp: str = ""
    org: str = ""
    asn: str = ""
    timezone: str = ""
    source: str = ""


class Term:
    def __init__(self, *, color: bool, links: bool) -> None:
        self.color = bool(color)
        self.links = bool(links)

    def _esc(self, s: str) -> str:
        if not self.color:
            return s
        return s

    def style(self, text: str, code: str) -> str:
        if not self.color:
            return text
        return f"\x1b[{code}m{text}\x1b[0m"

    def dim(self, text: str) -> str:
        return self.style(text, "2")

    def bold(self, text: str) -> str:
        return self.style(text, "1")

    def fg(self, text: str, color_code_256: int, *, bold: bool = False) -> str:
        if not self.color:
            return text
        base = f"38;5;{int(color_code_256)}"
        code = f"1;{base}" if bold else base
        return self.style(text, code)

    def rgb(self, text: str, r: int, g: int, b: int, *, bold: bool = False) -> str:
        if not self.color:
            return text
        r = max(0, min(int(r), 255))
        g = max(0, min(int(g), 255))
        b = max(0, min(int(b), 255))
        base = f"38;2;{r};{g};{b}"
        code = f"1;{base}" if bold else base
        return self.style(text, code)

    def bg_rgb(self, text: str, r: int, g: int, b: int) -> str:
        if not self.color:
            return text
        r = max(0, min(int(r), 255))
        g = max(0, min(int(g), 255))
        b = max(0, min(int(b), 255))
        return self.style(text, f"48;2;{r};{g};{b}")

    def ok(self, text: str) -> str:
        return self.rgb(text, 82, 255, 168, bold=True)

    def warn(self, text: str) -> str:
        return self.rgb(text, 255, 184, 107, bold=True)

    def bad(self, text: str) -> str:
        return self.rgb(text, 255, 92, 122, bold=True)

    def info(self, text: str) -> str:
        return self.rgb(text, 69, 183, 255, bold=True)

    def neon(self, text: str) -> str:
        return self.rgb(text, 82, 255, 168, bold=True)

    def violet(self, text: str, *, bold: bool = False) -> str:
        return self.rgb(text, 183, 124, 255, bold=bold)

    def cyan(self, text: str, *, bold: bool = False) -> str:
        return self.rgb(text, 69, 183, 255, bold=bold)

    def gray(self, text: str) -> str:
        return self.fg(text, 246)

    def rule(self, ch: str = "─") -> str:
        width = _terminal_width()
        sym = ch if self._supports_text(ch) else "-"
        return self.gray(sym * min(150, width))

    def bullet(self) -> str:
        return self.gray("-")

    def _supports_text(self, s: str) -> bool:
        try:
            enc = sys.stdout.encoding or "utf-8"
        except Exception:
            enc = "utf-8"
        try:
            s.encode(enc, errors="strict")
            return True
        except Exception:
            return False

    def tag(self, label: str, *, color: str = "cyan") -> str:
        lab = label.strip().upper()
        if not self.color:
            return lab
        inner = f" {lab} "
        if color == "green":
            return self.bg_rgb(self.rgb(inner, 5, 12, 9, bold=True), 10, 28, 20)
        if color == "violet":
            return self.bg_rgb(self.rgb(inner, 22, 12, 28, bold=True), 18, 10, 24)
        if color == "red":
            return self.bg_rgb(self.rgb(inner, 28, 10, 14, bold=True), 24, 8, 12)
        return self.bg_rgb(self.rgb(inner, 10, 16, 30, bold=True), 8, 14, 28)

    def link(self, text: str, url: str) -> str:
        if not self.links:
            return text
        if not sys.stdout.isatty():
            return text
        safe_url = url.replace("\x1b", "").replace("\r", "").replace("\n", "")
        safe_text = text.replace("\x1b", "").replace("\r", "").replace("\n", "")
        return f"\x1b]8;;{safe_url}\x1b\\{safe_text}\x1b]8;;\x1b\\"


_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m|\x1b\]8;;[^\x1b]*\x1b\\|\x1b\]8;;\x1b\\")


def _strip_ansi(s: str) -> str:
    return _ANSI_RE.sub("", s)


def _visible_len(s: str) -> int:
    return len(_strip_ansi(s))


def _terminal_width(default: int = 120) -> int:
    try:
        w = int(shutil.get_terminal_size((default, 20)).columns)
        return max(60, min(w, 240))
    except Exception:
        return default


def _wrap_text(text: str, width: int) -> List[str]:
    t = str(text or "").replace("\r", " ").replace("\n", " ").strip()
    if not t:
        return []
    if width <= 10:
        return [t[:width]]
    words = t.split()
    lines: List[str] = []
    cur = ""
    for w in words:
        if not cur:
            cur = w
            continue
        if len(cur) + 1 + len(w) <= width:
            cur = f"{cur} {w}"
        else:
            lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    out: List[str] = []
    for line in lines:
        if len(line) <= width:
            out.append(line)
            continue
        i = 0
        while i < len(line):
            out.append(line[i : i + width])
            i += width
    return out


def _truncate_middle(text: str, max_len: int) -> str:
    s = str(text or "")
    if max_len <= 0 or len(s) <= max_len:
        return s
    if max_len < 10:
        return s[: max_len - 1] + "…"
    left = (max_len - 1) // 2
    right = max_len - 1 - left
    return s[:left] + "…" + s[-right:]


def _sanitize_rdap_text(text: str, *, max_len: int, hide_cert: bool) -> str:
    t = str(text or "")
    if hide_cert and "-----BEGIN CERTIFICATE-----" in t:
        return "[certificate omitted]"
    if hide_cert:
        t = re.sub(r"-----BEGIN [^-]+-----[\s\S]*?-----END [^-]+-----", "[block omitted]", t)
    t = t.replace("\r", "\n")
    t = re.sub(r"\n{3,}", "\n\n", t).strip()
    if max_len > 0 and len(t) > max_len:
        return t[: max_len - 1] + "…"
    return t


def default_color_enabled() -> bool:
    if not sys.stdout.isatty():
        return False
    if os.environ.get("NO_COLOR"):
        return False
    return True


def default_links_enabled() -> bool:
    return sys.stdout.isatty()


def parse_bool_flag(val: Optional[bool], default: bool) -> bool:
    if val is None:
        return default
    return bool(val)


def url_google_maps(lat: float, lon: float) -> str:
    return f"https://www.google.com/maps?q={lat:.6f},{lon:.6f}"


def url_openstreetmap(lat: float, lon: float, zoom: int = 12) -> str:
    return f"https://www.openstreetmap.org/?mlat={lat:.6f}&mlon={lon:.6f}#map={int(zoom)}/{lat:.6f}/{lon:.6f}"


def url_ipinfo(ip: str) -> str:
    return f"https://ipinfo.io/{urllib.parse.quote(ip)}"


def url_whois_domain(domain: str) -> str:
    return f"https://who.is/whois/{urllib.parse.quote(domain)}"


def url_whois_ip(ip: str) -> str:
    return f"https://who.is/whois-ip/ip-address/{urllib.parse.quote(ip)}"


def url_bgp_asn(asn: str) -> str:
    return f"https://bgp.he.net/{urllib.parse.quote(asn)}"


def url_dns_google(domain: str) -> str:
    return f"https://dns.google/query?name={urllib.parse.quote(domain)}"


def looks_like_ip(s: str) -> bool:
    try:
        ipaddress.ip_address(s.strip().strip("[]"))
        return True
    except ValueError:
        return False


def looks_like_domain(s: str) -> bool:
    s = s.strip().strip(".")
    if not s or "." not in s:
        return False
    if looks_like_ip(s):
        return False
    return True


def _http_get_json(url: str, timeout_s: float) -> Dict[str, Any]:
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "IP-SCAN/1.0 (+terminal)",
            "Accept": "application/json",
        },
        method="GET",
    )
    with urllib.request.urlopen(req, timeout=timeout_s) as resp:
        raw = resp.read()
    try:
        return json.loads(raw.decode("utf-8", errors="replace"))
    except json.JSONDecodeError:
        return {}


def _http_get_json_rdap(url: str, timeout_s: float) -> Dict[str, Any]:
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "IP-SCAN/1.0 (+terminal)",
            "Accept": "application/rdap+json, application/json",
        },
        method="GET",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            raw = resp.read()
    except urllib.error.HTTPError as e:
        raw = e.read() if hasattr(e, "read") else b""
        try:
            return json.loads(raw.decode("utf-8", errors="replace"))
        except json.JSONDecodeError:
            return {}
    try:
        return json.loads(raw.decode("utf-8", errors="replace"))
    except json.JSONDecodeError:
        return {}


def rdap_servers_for_ip(ip: str) -> List[str]:
    return [
        f"https://rdap.arin.net/registry/ip/{urllib.parse.quote(ip)}",
        f"https://rdap.db.ripe.net/ip/{urllib.parse.quote(ip)}",
        f"https://rdap.apnic.net/ip/{urllib.parse.quote(ip)}",
        f"https://rdap.lacnic.net/rdap/ip/{urllib.parse.quote(ip)}",
        f"https://rdap.afrinic.net/rdap/ip/{urllib.parse.quote(ip)}",
    ]


def rdap_lookup_ip(ip: str, timeout_s: float) -> Tuple[Optional[str], Dict[str, Any]]:
    for url in rdap_servers_for_ip(ip):
        try:
            data = _http_get_json_rdap(url, timeout_s=timeout_s)
        except (urllib.error.URLError, TimeoutError, OSError, ValueError):
            data = {}
        if not data:
            continue
        if isinstance(data, dict) and data.get("errorCode") in (400, 404, 410):
            continue
        if isinstance(data, dict) and (data.get("startAddress") or data.get("handle") or data.get("name")):
            return url, data
    return None, {}


def _rdap_first_str(v: Any) -> str:
    if v is None:
        return ""
    if isinstance(v, str):
        return v
    if isinstance(v, (int, float)):
        return str(v)
    if isinstance(v, list):
        for it in v:
            s = _rdap_first_str(it)
            if s:
                return s
        return ""
    if isinstance(v, dict):
        return ""
    return str(v)


def _rdap_event_date(events: Any, action: str) -> str:
    if not isinstance(events, list):
        return ""
    for ev in events:
        if not isinstance(ev, dict):
            continue
        if str(ev.get("eventAction") or "").lower() == action.lower():
            return str(ev.get("eventDate") or "")
    return ""


def _rdap_extract_cidrs(data: Dict[str, Any]) -> List[str]:
    out: List[str] = []
    cidrs = data.get("cidr0_cidrs")
    if isinstance(cidrs, list):
        for c in cidrs:
            if not isinstance(c, dict):
                continue
            v4p = c.get("v4prefix")
            v6p = c.get("v6prefix")
            length = c.get("length")
            if v4p and length is not None:
                out.append(f"{v4p}/{length}")
            elif v6p and length is not None:
                out.append(f"{v6p}/{length}")
    return sorted(set(out))


def _rdap_extract_links(data: Dict[str, Any]) -> Dict[str, str]:
    out: Dict[str, str] = {}
    links = data.get("links")
    if not isinstance(links, list):
        return out
    for link in links:
        if not isinstance(link, dict):
            continue
        rel = str(link.get("rel") or "")
        href = str(link.get("href") or "")
        if rel and href and rel not in out:
            out[rel] = href
    return out


def _rdap_parse_vcard(entity: Dict[str, Any]) -> Dict[str, List[str]]:
    out: Dict[str, List[str]] = {"name": [], "email": [], "tel": [], "adr": []}
    vca = entity.get("vcardArray")
    if not (isinstance(vca, list) and len(vca) == 2 and isinstance(vca[1], list)):
        return out
    for item in vca[1]:
        if not (isinstance(item, list) and len(item) >= 4):
            continue
        key = str(item[0] or "").lower()
        val = item[3]
        if key == "fn":
            s = _rdap_first_str(val)
            if s:
                out["name"].append(s)
        elif key == "email":
            s = _rdap_first_str(val)
            if s:
                out["email"].append(s)
        elif key == "tel":
            s = _rdap_first_str(val)
            if s.startswith("tel:"):
                s = s[4:]
            if s:
                out["tel"].append(s)
        elif key == "adr":
            if isinstance(val, list):
                parts = [str(p).strip() for p in val if str(p).strip()]
                s = ", ".join(parts)
            else:
                s = _rdap_first_str(val)
            if s:
                out["adr"].append(s)
    for k in list(out.keys()):
        out[k] = sorted(set([x for x in out[k] if x]))
    return out


def _rdap_entities_by_role(data: Dict[str, Any], role: str) -> List[Dict[str, Any]]:
    ents = data.get("entities")
    if not isinstance(ents, list):
        return []
    out: List[Dict[str, Any]] = []
    for e in ents:
        if not isinstance(e, dict):
            continue
        roles = e.get("roles")
        if isinstance(roles, list) and any(str(r).lower() == role.lower() for r in roles):
            out.append(e)
    return out


def _rdap_walk_entities(data: Any) -> Iterable[Dict[str, Any]]:
    if not isinstance(data, dict):
        return []
    ents = data.get("entities")
    if not isinstance(ents, list):
        return []
    stack: List[Dict[str, Any]] = [e for e in ents if isinstance(e, dict)]
    out: List[Dict[str, Any]] = []
    while stack:
        e = stack.pop()
        out.append(e)
        sub = e.get("entities")
        if isinstance(sub, list):
            for se in sub:
                if isinstance(se, dict):
                    stack.append(se)
    return out


def _rdap_entities_by_role_recursive(data: Dict[str, Any], role: str) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for e in _rdap_walk_entities(data):
        roles = e.get("roles")
        if isinstance(roles, list) and any(str(r).lower() == role.lower() for r in roles):
            out.append(e)
    return out


def rdap_summarize_ip(data: Dict[str, Any]) -> Dict[str, Any]:
    start = str(data.get("startAddress") or "")
    end = str(data.get("endAddress") or "")
    handle = str(data.get("handle") or "")
    name = str(data.get("name") or "")
    parent = str(data.get("parentHandle") or "")
    net_type = str(data.get("type") or "")
    country = str(data.get("country") or "")
    events = data.get("events")
    reg = _rdap_event_date(events, "registration")
    updated = _rdap_event_date(events, "last changed") or _rdap_event_date(events, "last update of rdap database")
    cidrs = _rdap_extract_cidrs(data)
    links = _rdap_extract_links(data)
    remarks_out: List[str] = []
    remarks = data.get("remarks")
    if isinstance(remarks, list):
        for r in remarks:
            if not isinstance(r, dict):
                continue
            desc = r.get("description")
            if isinstance(desc, list):
                s = " ".join(str(x).strip() for x in desc if str(x).strip())
            else:
                s = str(desc or "").strip()
            if s:
                remarks_out.append(s)
    remarks_out = sorted(set(remarks_out))
    notices_out: List[str] = []
    notices = data.get("notices")
    if isinstance(notices, list):
        for n in notices:
            if not isinstance(n, dict):
                continue
            desc = n.get("description")
            if isinstance(desc, list):
                s = " ".join(str(x).strip() for x in desc if str(x).strip())
            else:
                s = str(desc or "").strip()
            if s:
                notices_out.append(s)
    notices_out = sorted(set(notices_out))

    origin_as = ""
    oa = data.get("originAutnums")
    if isinstance(oa, list):
        nums: List[str] = []
        for x in oa:
            try:
                n = int(x)
                nums.append(f"AS{n}")
            except Exception:
                continue
        origin_as = ", ".join(sorted(set(nums)))
    elif oa is not None:
        try:
            origin_as = f"AS{int(oa)}"
        except Exception:
            origin_as = str(oa)

    def entity_line(e: Dict[str, Any]) -> Dict[str, Any]:
        vc = _rdap_parse_vcard(e)
        return {
            "handle": str(e.get("handle") or ""),
            "roles": [str(r) for r in (e.get("roles") or [])] if isinstance(e.get("roles"), list) else [],
            "name": vc["name"],
            "email": vc["email"],
            "tel": vc["tel"],
            "adr": vc["adr"],
            "links": _rdap_extract_links(e),
        }

    org_entities = _rdap_entities_by_role_recursive(data, "registrant") or _rdap_entities_by_role_recursive(data, "administrative") or []
    org_name = ""
    org_id = ""
    if org_entities:
        org_name = _rdap_first_str(_rdap_parse_vcard(org_entities[0]).get("name")) or str(org_entities[0].get("handle") or "")
        org_id = str(org_entities[0].get("handle") or "")

    contacts: List[Dict[str, Any]] = []
    for role in ["noc", "technical", "abuse", "administrative", "registrant"]:
        for e in _rdap_entities_by_role_recursive(data, role):
            contacts.append(entity_line(e))

    if org_entities:
        contacts.insert(0, {"role": "org", **entity_line(org_entities[0])})

    deduped: List[Dict[str, Any]] = []
    seen_contact: Set[Tuple[Any, ...]] = set()
    for c in contacts:
        def norm_list(v: Any) -> List[str]:
            if v is None:
                return []
            if isinstance(v, list):
                return [str(x) for x in v if str(x)]
            return [str(v)] if str(v) else []

        roles = c.get("roles") or []
        if not isinstance(roles, list):
            roles = []
        names = norm_list(c.get("name"))
        emails = norm_list(c.get("email"))
        tels = norm_list(c.get("tel"))
        adrs = norm_list(c.get("adr"))
        key = (
            str(c.get("role") or ""),
            str(c.get("handle") or ""),
            tuple(sorted([str(r).lower() for r in roles])),
            tuple(names),
            tuple(emails),
            tuple(tels),
            tuple(adrs),
        )
        if key in seen_contact:
            continue
        seen_contact.add(key)
        deduped.append(c)
    contacts = deduped

    statuses: List[str] = []
    st = data.get("status")
    if isinstance(st, list):
        statuses = sorted(set([str(x) for x in st if str(x)]))

    return {
        "NetRange": (f"{start} - {end}".strip(" -") if start or end else ""),
        "CIDR": ", ".join(cidrs),
        "NetName": name,
        "NetHandle": handle,
        "Parent": parent,
        "NetType": net_type,
        "OriginAS": origin_as,
        "Country": country,
        "RegDate": reg,
        "Updated": updated,
        "Status": ", ".join(statuses),
        "Remarks": remarks_out,
        "Notices": notices_out,
        "Ref": links.get("self") or "",
        "OrgName": org_name,
        "OrgId": org_id,
        "Contacts": contacts,
        "Links": links,
    }


def print_rdap_block(idx: int, ip: str, rdap_url: str, summary: Dict[str, Any], term: Term) -> None:
    width = _terminal_width()
    key_w = 12
    src = ""
    try:
        src = urllib.parse.urlparse(rdap_url).hostname or ""
    except Exception:
        src = ""
    head = term.tag("RDAP", color="violet") + term.dim("  ") + term.cyan(term.link(ip, rdap_url), bold=True)
    if src:
        head += term.gray("  @  ") + term.gray(src)
    print("  " + head)

    def fmt_key(k: str) -> str:
        return term.gray(f"{k}:").rjust(key_w)

    def fmt_val(k: str, s: str) -> str:
        v = str(s or "").strip()
        if not v:
            return v
        lk = k.lower()
        if lk in ("netrange", "cidr"):
            return term.cyan(v, bold=True)
        if lk in ("netname",):
            return term.violet(v, bold=True)
        if lk in ("nethandle", "parent"):
            return term.gray(v)
        if lk in ("nettype",):
            return term.gray(v)
        if lk in ("status",):
            low = v.lower()
            if "active" in low or "allocated" in low:
                return term.ok(v)
            if "reserved" in low or "inactive" in low:
                return term.bad(v)
            return term.warn(v)
        if lk in ("country",):
            return term.violet(v, bold=True)
        if lk in ("orgname",):
            return term.neon(v)
        if lk in ("orgid",):
            return term.cyan(v, bold=True)
        if lk in ("regdate", "updated"):
            return term.gray(v)
        if lk in ("originas",):
            tokens = [t.strip().upper() for t in re.split(r"[,\s]+", v) if t.strip()]
            asns = [t if t.startswith("AS") else f"AS{t}" for t in tokens]
            parts: List[str] = []
            for a in asns[:12]:
                parts.append(term.violet(term.link(a, url_bgp_asn(a)), bold=True))
            return ", ".join(parts) if parts else term.gray(v)
        if lk in ("ref",) and v.startswith("http"):
            return term.cyan(term.link(v, v), bold=True)
        return term.gray(v)

    fields = [
        ("NetRange", summary.get("NetRange")),
        ("CIDR", summary.get("CIDR")),
        ("NetName", summary.get("NetName")),
        ("NetHandle", summary.get("NetHandle")),
        ("Parent", summary.get("Parent")),
        ("NetType", summary.get("NetType")),
        ("OriginAS", summary.get("OriginAS")),
        ("Status", summary.get("Status")),
        ("Country", summary.get("Country")),
        ("OrgName", summary.get("OrgName")),
        ("OrgId", summary.get("OrgId")),
        ("RegDate", summary.get("RegDate")),
        ("Updated", summary.get("Updated")),
        ("Ref", summary.get("Ref")),
    ]
    for k, v in fields:
        s = str(v or "").strip()
        if not s:
            continue
        if k == "Ref" and s.startswith("http"):
            left = fmt_key(k)
            prefix = f"  {left} "
            print(prefix + fmt_val(k, s))
            continue
        left = fmt_key(k)
        prefix = f"  {left} "
        indent = _visible_len(prefix)
        wrapped = _wrap_text(_strip_ansi(str(fmt_val(k, s))), max(20, width - indent))
        if not wrapped:
            continue
        val = fmt_val(k, s)
        if _visible_len(val) <= max(20, width - indent):
            print(prefix + val)
        else:
            print(prefix + term.gray(wrapped[0]))
            for more in wrapped[1:3]:
                print(" " * indent + term.gray(more))
    remarks = summary.get("Remarks")
    if isinstance(remarks, list) and remarks:
        clean = [_sanitize_rdap_text(x, max_len=1400, hide_cert=True) for x in remarks if str(x or "").strip()]
        if clean:
            left = fmt_key("Comment")
            prefix = f"  {left} "
            indent = _visible_len(prefix)
            for i, item in enumerate(clean[:2]):
                if i == 0:
                    pfx = prefix
                else:
                    pfx = " " * indent
                wrapped = _wrap_text(item, max(20, width - indent))
                if not wrapped:
                    continue
                print(pfx + term.gray(wrapped[0]))
                for more in wrapped[1:4]:
                    print(" " * indent + term.gray(more))
    notices = summary.get("Notices")
    if isinstance(notices, list) and notices:
        clean = [_sanitize_rdap_text(x, max_len=800, hide_cert=True) for x in notices if str(x or "").strip()]
        if clean:
            left = fmt_key("Notices")
            prefix = f"  {left} "
            indent = _visible_len(prefix)
            for i, item in enumerate(clean[:2]):
                if i == 0:
                    pfx = prefix
                else:
                    pfx = " " * indent
                wrapped = _wrap_text(item, max(20, width - indent))
                if not wrapped:
                    continue
                print(pfx + term.gray(wrapped[0]))
                for more in wrapped[1:4]:
                    print(" " * indent + term.gray(more))
    contacts = summary.get("Contacts")
    if isinstance(contacts, list) and contacts:
        left = term.gray("Contacts:").rjust(key_w)
        print(f"  {left}")
        seen_lines: Set[str] = set()
        for c in contacts[:12]:
            role = ",".join(c.get("roles") or []) if isinstance(c, dict) else ""
            role = role or str(c.get("role") or "")
            role = role or "contact"
            name = ", ".join(c.get("name") or []) if isinstance(c, dict) else ""
            email = ", ".join(c.get("email") or []) if isinstance(c, dict) else ""
            tel = ", ".join(c.get("tel") or []) if isinstance(c, dict) else ""
            adr = ", ".join(c.get("adr") or []) if isinstance(c, dict) else ""
            handle = str(c.get("handle") or "") if isinstance(c, dict) else ""
            line = f"    {term.bullet()} {term.rgb(role.upper(), 120, 200, 255, bold=True)}"
            if handle:
                line += term.gray(" :: ") + term.gray(handle)
            if name:
                line += term.gray(" :: ") + term.violet(name)
            if email:
                line += term.gray(" :: ") + term.cyan(email)
            if tel:
                line += term.gray(" :: ") + term.neon(tel)
            if adr:
                line += term.gray(" :: ") + term.gray(adr)
            if line in seen_lines:
                continue
            seen_lines.add(line)
            print(line)


def _top_counts(items: List[str], n: int) -> List[Tuple[str, int]]:
    counts: Dict[str, int] = {}
    for it in items:
        s = str(it or "").strip()
        if not s:
            continue
        counts[s] = counts.get(s, 0) + 1
    return sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:n]


def _try_http_request(url: str, timeout_s: float) -> Tuple[int, str, Dict[str, str], bytes]:
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "IP-SCAN/1.0 (+terminal)",
            "Accept": "*/*",
        },
        method="GET",
    )
    with urllib.request.urlopen(req, timeout=timeout_s) as resp:
        status = int(getattr(resp, "status", 0) or 0)
        final_url = str(getattr(resp, "geturl", lambda: url)())
        headers = {str(k): str(v) for k, v in resp.headers.items()}
        body = resp.read(60_000)
    return status, final_url, headers, body


def http_probe(host: str, timeout_s: float) -> Dict[str, Any]:
    out: Dict[str, Any] = {"host": host, "results": []}
    schemes = ["https", "http"]
    for sch in schemes:
        url = f"{sch}://{host}/"
        try:
            status, final_url, headers, body = _try_http_request(url, timeout_s)
            text = body.decode("utf-8", errors="replace")
            title = ""
            m = re.search(r"<title[^>]*>(.*?)</title>", text, flags=re.IGNORECASE | re.DOTALL)
            if m:
                title = re.sub(r"\s+", " ", m.group(1)).strip()
            out["results"].append(
                {
                    "url": url,
                    "status": status,
                    "final_url": final_url,
                    "server": headers.get("Server", ""),
                    "powered_by": headers.get("X-Powered-By", ""),
                    "content_type": headers.get("Content-Type", ""),
                    "content_length": headers.get("Content-Length", ""),
                    "hsts": headers.get("Strict-Transport-Security", ""),
                    "csp": headers.get("Content-Security-Policy", ""),
                    "xfo": headers.get("X-Frame-Options", ""),
                    "xxp": headers.get("X-XSS-Protection", ""),
                    "xcto": headers.get("X-Content-Type-Options", ""),
                    "refpol": headers.get("Referrer-Policy", ""),
                    "permissions": headers.get("Permissions-Policy", ""),
                    "title": title,
                }
            )
        except Exception as e:
            out["results"].append({"url": url, "error": str(e)})
    return out


def tls_probe(host: str, timeout_s: float) -> Dict[str, Any]:
    out: Dict[str, Any] = {"host": host, "ok": False}
    ctx = ssl.create_default_context()
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    try:
        with socket.create_connection((host, 443), timeout=timeout_s) as sock:
            with ctx.wrap_socket(sock, server_hostname=host) as ssock:
                cert = ssock.getpeercert()
                out["ok"] = True
                out["protocol"] = str(ssock.version() or "")
                out["cipher"] = " ".join(str(x) for x in (ssock.cipher() or ()) if x)
                out["subject"] = cert.get("subject")
                out["issuer"] = cert.get("issuer")
                out["notBefore"] = cert.get("notBefore", "")
                out["notAfter"] = cert.get("notAfter", "")
                out["subjectAltName"] = cert.get("subjectAltName")
    except Exception as e:
        out["error"] = str(e)
    return out


def print_http_block(host: str, http_data: Dict[str, Any], tls_data: Optional[Dict[str, Any]], term: Term) -> None:
    width = _terminal_width()
    print("")
    print(term.tag("HTTP", color="cyan") + term.dim("  ") + term.cyan(term.link(host, f"https://{host}/"), bold=True))
    results = http_data.get("results") if isinstance(http_data, dict) else None
    if not isinstance(results, list):
        print(term.gray("  (no data)"))
        return
    for r in results:
        if not isinstance(r, dict):
            continue
        url = str(r.get("url") or "")
        if r.get("error"):
            print(f"  {term.bullet()} {term.link(url, url)} {term.gray('->')} {term.bad('ERR')} {term.gray(str(r.get('error') or ''))}")
            continue
        status = int(r.get("status") or 0)
        final_url = str(r.get("final_url") or "")
        st = term.ok(str(status)) if 200 <= status < 400 else term.warn(str(status)) if status else term.bad("0")
        line = f"  {term.bullet()} {term.link(url, url)} {term.gray('->')} {st}"
        if final_url and final_url != url:
            line += term.gray(" :: ") + term.link(_truncate_middle(final_url, 80), final_url)
        print(line)
        title = str(r.get("title") or "").strip()
        if title:
            print(f"    {term.gray('title:')} {term.violet(_truncate_middle(title, max(40, width - 16)))}")
        server = str(r.get("server") or "").strip()
        powered = str(r.get("powered_by") or "").strip()
        ctype = str(r.get("content_type") or "").strip()
        if server or powered or ctype:
            bits = []
            if server:
                bits.append(f"server={server}")
            if powered:
                bits.append(f"x-powered-by={powered}")
            if ctype:
                bits.append(f"type={ctype}")
            print(f"    {term.gray('info:')} {term.gray(_truncate_middle(' | '.join(bits), max(50, width - 16)))}")
        sec = []
        for k in ["hsts", "csp", "xfo", "xcto", "refpol", "permissions"]:
            v = str(r.get(k) or "").strip()
            if v:
                sec.append(k.upper())
        if sec:
            print(f"    {term.gray('sec:')} {term.neon(', '.join(sec))}")
    if tls_data:
        print(term.tag("TLS", color="violet") + term.dim("  ") + term.violet(host, bold=True))
        if not tls_data.get("ok"):
            print(f"  {term.bullet()} {term.bad('ERR')} {term.gray(str(tls_data.get('error') or ''))}")
            return
        proto = str(tls_data.get("protocol") or "")
        cipher = str(tls_data.get("cipher") or "")
        nb = str(tls_data.get("notBefore") or "")
        na = str(tls_data.get("notAfter") or "")
        if proto or cipher:
            print(f"  {term.bullet()} {term.cyan(proto, bold=True)} {term.gray('|')} {term.gray(cipher)}")
        if nb or na:
            print(f"  {term.bullet()} {term.gray('valid:')} {term.gray(nb)} {term.gray('->')} {term.gray(na)}")
        san = tls_data.get("subjectAltName")
        if isinstance(san, list) and san:
            names = [str(v) for (t, v) in san if str(t) == "DNS" and str(v)]
            if names:
                print(f"  {term.bullet()} {term.gray('san:')} " + term.gray(_truncate_middle(", ".join(names[:20]), max(50, width - 10))))


def geo_ip_api_com(ip: str, timeout_s: float) -> Optional[GeoResult]:
    fields = ",".join(
        [
            "status",
            "message",
            "query",
            "country",
            "regionName",
            "city",
            "lat",
            "lon",
            "isp",
            "org",
            "as",
            "timezone",
        ]
    )
    url = f"http://ip-api.com/json/{urllib.parse.quote(ip)}?fields={urllib.parse.quote(fields)}"
    data = _http_get_json(url, timeout_s=timeout_s)
    if data.get("status") != "success":
        return None
    lat = data.get("lat")
    lon = data.get("lon")
    if lat is None or lon is None:
        return None
    return GeoResult(
        ip=str(data.get("query") or ip),
        input=ip,
        lat=float(lat),
        lon=float(lon),
        country=str(data.get("country") or ""),
        region=str(data.get("regionName") or ""),
        city=str(data.get("city") or ""),
        isp=str(data.get("isp") or ""),
        org=str(data.get("org") or ""),
        asn=str(data.get("as") or ""),
        timezone=str(data.get("timezone") or ""),
        source="ip-api.com",
    )


def geo_ipapi_co(ip: str, timeout_s: float) -> Optional[GeoResult]:
    url = f"https://ipapi.co/{urllib.parse.quote(ip)}/json/"
    data = _http_get_json(url, timeout_s=timeout_s)
    if not data or data.get("error"):
        return None
    lat = data.get("latitude")
    lon = data.get("longitude")
    if lat is None or lon is None:
        return None
    return GeoResult(
        ip=ip,
        input=ip,
        lat=float(lat),
        lon=float(lon),
        country=str(data.get("country_name") or ""),
        region=str(data.get("region") or ""),
        city=str(data.get("city") or ""),
        isp=str(data.get("org") or ""),
        org=str(data.get("org") or ""),
        asn=str(data.get("asn") or ""),
        timezone=str(data.get("timezone") or ""),
        source="ipapi.co",
    )


def resolve_target(target: str) -> Tuple[str, List[str]]:
    raw = target.strip()
    if not raw:
        return target, []
    if "://" in raw:
        parsed = urllib.parse.urlparse(raw)
        host = parsed.hostname or raw
    else:
        host = raw
    host = host.strip("[]")
    try:
        ip = ipaddress.ip_address(host)
        return target, [str(ip)]
    except ValueError:
        pass
    ips: Set[str] = set()
    try:
        infos = socket.getaddrinfo(host, None, proto=socket.IPPROTO_TCP)
        for family, _, _, _, sockaddr in infos:
            if family == socket.AF_INET:
                ips.add(sockaddr[0])
            elif family == socket.AF_INET6:
                ips.add(sockaddr[0])
    except socket.gaierror:
        return target, []
    return target, sorted(ips)


def _dns_encode_name(name: str) -> bytes:
    labels = [p for p in name.strip(".").split(".") if p]
    out = bytearray()
    for lab in labels:
        b = lab.encode("utf-8", errors="strict")
        if len(b) > 63:
            raise ValueError("Label terlalu panjang")
        out.append(len(b))
        out.extend(b)
    out.append(0)
    return bytes(out)


def _dns_read_u16(data: bytes, off: int) -> Tuple[int, int]:
    if off + 2 > len(data):
        raise ValueError("DNS packet rusak")
    return (data[off] << 8) | data[off + 1], off + 2


def _dns_read_u32(data: bytes, off: int) -> Tuple[int, int]:
    if off + 4 > len(data):
        raise ValueError("DNS packet rusak")
    v = (data[off] << 24) | (data[off + 1] << 16) | (data[off + 2] << 8) | data[off + 3]
    return v, off + 4


def _dns_read_name(data: bytes, off: int) -> Tuple[str, int]:
    labels: List[str] = []
    jumped = False
    seen_ptr = 0
    start = off
    while True:
        if off >= len(data):
            raise ValueError("DNS packet rusak")
        ln = data[off]
        if ln == 0:
            off += 1
            break
        if (ln & 0xC0) == 0xC0:
            if off + 1 >= len(data):
                raise ValueError("DNS packet rusak")
            ptr = ((ln & 0x3F) << 8) | data[off + 1]
            off += 2
            if not jumped:
                start = off
                jumped = True
            seen_ptr += 1
            if seen_ptr > 20:
                raise ValueError("DNS pointer loop")
            off = ptr
            continue
        off += 1
        if off + ln > len(data):
            raise ValueError("DNS packet rusak")
        labels.append(data[off : off + ln].decode("utf-8", errors="replace"))
        off += ln
    name = ".".join(labels)
    return name, (start if jumped else off)


def _dns_build_query(qname: str, qtype: int) -> Tuple[int, bytes]:
    txid = secrets.randbelow(65536)
    flags = 0x0100
    header = struct.pack("!HHHHHH", txid, flags, 1, 0, 0, 0)
    question = _dns_encode_name(qname) + struct.pack("!HH", qtype, 1)
    return txid, header + question


def _dns_parse_response(data: bytes, txid: int) -> Dict[str, Any]:
    if len(data) < 12:
        raise ValueError("DNS packet terlalu pendek")
    rxid, flags, qd, an, ns, ar = struct.unpack("!HHHHHH", data[:12])
    if rxid != txid:
        raise ValueError("DNS txid tidak cocok")
    tc = bool(flags & 0x0200)
    rcode = flags & 0x000F
    off = 12
    for _ in range(qd):
        _, off = _dns_read_name(data, off)
        _, off = _dns_read_u16(data, off)
        _, off = _dns_read_u16(data, off)

    def parse_rr(count: int) -> List[Dict[str, Any]]:
        nonlocal off
        out: List[Dict[str, Any]] = []
        for _ in range(count):
            name, off = _dns_read_name(data, off)
            rtype, off = _dns_read_u16(data, off)
            rclass, off = _dns_read_u16(data, off)
            ttl, off = _dns_read_u32(data, off)
            rdlen, off = _dns_read_u16(data, off)
            rdoff = off
            off += rdlen
            if rdoff + rdlen > len(data):
                raise ValueError("DNS rdata keluar batas")
            out.append(
                {
                    "name": name,
                    "type": rtype,
                    "class": rclass,
                    "ttl": ttl,
                    "rdata": data[rdoff : rdoff + rdlen],
                    "rdoff": rdoff,
                }
            )
        return out

    answers = parse_rr(an)
    authorities = parse_rr(ns)
    additionals = parse_rr(ar)
    return {"tc": tc, "rcode": rcode, "answers": answers, "authorities": authorities, "additionals": additionals}


def _dns_decode_rdata(rr: Dict[str, Any], packet: bytes) -> Optional[str]:
    rtype = rr["type"]
    rdata: bytes = rr["rdata"]
    rdoff: int = rr["rdoff"]
    if rtype == 1 and len(rdata) == 4:
        return socket.inet_ntop(socket.AF_INET, rdata)
    if rtype == 28 and len(rdata) == 16:
        return socket.inet_ntop(socket.AF_INET6, rdata)
    if rtype in (2, 5, 12):
        name, _ = _dns_read_name(packet, rdoff)
        return name
    if rtype == 15:
        if len(rdata) < 3:
            return None
        pref = (rdata[0] << 8) | rdata[1]
        host, _ = _dns_read_name(packet, rdoff + 2)
        return f"{pref} {host}"
    if rtype == 16:
        parts: List[str] = []
        i = 0
        while i < len(rdata):
            ln = rdata[i]
            i += 1
            if i + ln > len(rdata):
                break
            parts.append(rdata[i : i + ln].decode("utf-8", errors="replace"))
            i += ln
        return " ".join(parts).strip()
    if rtype == 6:
        mname, off = _dns_read_name(packet, rdoff)
        rname, off = _dns_read_name(packet, off)
        if off + 20 > len(packet):
            return f"{mname} {rname}"
        serial, off = _dns_read_u32(packet, off)
        refresh, off = _dns_read_u32(packet, off)
        retry, off = _dns_read_u32(packet, off)
        expire, off = _dns_read_u32(packet, off)
        minimum, _ = _dns_read_u32(packet, off)
        return f"{mname} {rname} serial={serial} refresh={refresh} retry={retry} expire={expire} minimum={minimum}"
    if rtype == 257:
        if len(rdata) < 3:
            return None
        flags = int(rdata[0])
        tag_len = int(rdata[1])
        if 2 + tag_len > len(rdata):
            return None
        tag = rdata[2 : 2 + tag_len].decode("utf-8", errors="replace")
        value = rdata[2 + tag_len :].decode("utf-8", errors="replace").strip()
        return f"{flags} {tag} {value}".strip()
    return None


def dns_query(
    qname: str,
    qtype: int,
    *,
    dns_servers: List[str],
    timeout_s: float,
) -> Tuple[bool, List[str]]:
    last_err: Optional[Exception] = None
    for server in dns_servers:
        txid, pkt = _dns_build_query(qname, qtype)
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
                s.settimeout(timeout_s)
                s.sendto(pkt, (server, 53))
                data, _ = s.recvfrom(4096)
            parsed = _dns_parse_response(data, txid)
            if parsed["rcode"] != 0:
                return parsed["tc"], []
            vals: List[str] = []
            for rr in parsed["answers"]:
                if int(rr.get("type") or 0) != int(qtype):
                    continue
                v = _dns_decode_rdata(rr, data)
                if v:
                    vals.append(v)
            return parsed["tc"], vals
        except Exception as e:
            last_err = e
            continue
    if last_err is not None:
        return False, []
    return False, []


def dns_lookup_all(domain: str, *, dns_servers: List[str], timeout_s: float) -> Dict[str, List[str]]:
    qname = domain.strip().strip(".")
    if not qname:
        return {}
    out: Dict[str, List[str]] = {}
    qtypes: List[Tuple[str, int]] = [
        ("CNAME", 5),
        ("A", 1),
        ("AAAA", 28),
        ("NS", 2),
        ("MX", 15),
        ("TXT", 16),
        ("SOA", 6),
        ("CAA", 257),
    ]
    for label, qtype in qtypes:
        _, vals = dns_query(qname, qtype, dns_servers=dns_servers, timeout_s=timeout_s)
        if vals:
            uniq = sorted(set(vals))
            out[label] = uniq
    return out


def dns_lookup_ips(name: str, *, dns_servers: List[str], timeout_s: float) -> List[str]:
    qname = name.strip().strip(".")
    if not qname:
        return []
    _, a = dns_query(qname, 1, dns_servers=dns_servers, timeout_s=timeout_s)
    _, aaaa = dns_query(qname, 28, dns_servers=dns_servers, timeout_s=timeout_s)
    return sorted(set([*a, *aaaa]))


def dns_lookup_txt(name: str, *, dns_servers: List[str], timeout_s: float) -> List[str]:
    qname = name.strip().strip(".")
    if not qname:
        return []
    _, vals = dns_query(qname, 16, dns_servers=dns_servers, timeout_s=timeout_s)
    return sorted(set(vals))


def dns_security_profile(domain: str, *, dns_servers: List[str], timeout_s: float) -> Dict[str, List[str]]:
    d = domain.strip().strip(".")
    out: Dict[str, List[str]] = {}
    for name, q in [
        ("DMARC", f"_dmarc.{d}"),
        ("MTA-STS", f"_mta-sts.{d}"),
        ("TLS-RPT", f"_smtp._tls.{d}"),
    ]:
        vals = dns_lookup_txt(q, dns_servers=dns_servers, timeout_s=timeout_s)
        if vals:
            out[name] = vals
    return out

def _extract_hosts_from_dns_info(domain: str, info: Dict[str, List[str]]) -> List[str]:
    out: List[str] = []
    for ns in info.get("NS", []) or []:
        out.append(ns.strip().strip("."))
    for mx in info.get("MX", []) or []:
        parts = mx.split()
        host = parts[-1] if parts else mx
        out.append(host.strip().strip("."))
    for cn in info.get("CNAME", []) or []:
        out.append(cn.strip().strip("."))
    www = f"www.{domain.strip().strip('.')}"
    if www and www.lower() != domain.strip().strip(".").lower():
        out.append(www)
    uniq: List[str] = []
    seen: Set[str] = set()
    for h in out:
        if not h:
            continue
        hl = h.lower()
        if hl in seen:
            continue
        seen.add(hl)
        uniq.append(h)
    return uniq


def _dns_reverse_name(ip: str) -> Optional[str]:
    try:
        addr = ipaddress.ip_address(ip)
    except ValueError:
        return None
    if isinstance(addr, ipaddress.IPv4Address):
        parts = ip.split(".")
        if len(parts) != 4:
            return None
        parts.reverse()
        return ".".join(parts) + ".in-addr.arpa"
    if isinstance(addr, ipaddress.IPv6Address):
        hex32 = addr.exploded.replace(":", "")
        nibbles = list(hex32)
        nibbles.reverse()
        return ".".join(nibbles) + ".ip6.arpa"
    return None


def dns_ptr_lookup(ip: str, *, dns_servers: List[str], timeout_s: float) -> List[str]:
    rev = _dns_reverse_name(ip)
    if not rev:
        return []
    _, vals = dns_query(rev, 12, dns_servers=dns_servers, timeout_s=timeout_s)
    return sorted(set(vals))


def is_domain_like(s: str) -> bool:
    s = s.strip()
    if not s:
        return False
    if "://" in s:
        try:
            host = urllib.parse.urlparse(s).hostname
        except Exception:
            host = None
        if host:
            s = host
    s = s.strip("[]")
    try:
        ipaddress.ip_address(s)
        return False
    except ValueError:
        pass
    try:
        ipaddress.ip_network(s, strict=False)
        return False
    except ValueError:
        pass
    if "." not in s:
        return False
    return True


def print_domain_info(domain: str, info: Dict[str, List[str]], *, dns_servers: List[str], timeout_s: float, term: Term) -> None:
    print("")
    dom_raw = domain
    dom = term.link(dom_raw, url_dns_google(dom_raw)) if looks_like_domain(dom_raw) else dom_raw
    print(term.tag("DOMAIN", color="cyan") + term.dim("  ") + term.cyan(dom, bold=True))
    if not info:
        print(term.gray("DNS: tidak ada data atau gagal query."))
        return
    order = ["CNAME", "A", "AAAA", "NS", "MX", "TXT", "SOA"]
    for k in order:
        vals = info.get(k)
        if not vals:
            continue
        print(term.violet(k, bold=True) + term.gray(":"))
        for v in vals:
            vv = v
            if looks_like_ip(v):
                vv = term.cyan(term.link(v, url_ipinfo(v)))
            elif looks_like_domain(v.split()[-1]):
                d = v.split()[-1]
                vv = v.replace(d, term.violet(term.link(d, url_whois_domain(d))))
            print(f"  {term.bullet()} {vv}")
    ips = (info.get("A") or []) + (info.get("AAAA") or [])
    if ips:
        ptr_map: List[Tuple[str, List[str]]] = []
        for ip in ips:
            ptrs = dns_ptr_lookup(ip, dns_servers=dns_servers, timeout_s=timeout_s)
            if ptrs:
                ptr_map.append((ip, ptrs))
        if ptr_map:
            print(term.violet("PTR", bold=True) + term.gray(":"))
            for ip, ptrs in ptr_map:
                for p in ptrs:
                    left = term.cyan(term.link(ip, url_ipinfo(ip)))
                    right = term.violet(term.link(p, url_whois_domain(p))) if looks_like_domain(p) else p
                    print(f"  {term.bullet()} {left} {term.gray('->')} {right}")


def expand_targets(items: Iterable[str]) -> List[str]:
    expanded: List[str] = []
    for item in items:
        t = item.strip()
        if not t or t.startswith("#"):
            continue
        try:
            net = ipaddress.ip_network(t, strict=False)
            expanded.extend(str(ip) for ip in net.hosts())
            continue
        except ValueError:
            expanded.append(t)
    return expanded


def read_targets_from_file(path: str) -> List[str]:
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        return [line.rstrip("\n") for line in f]


def is_public_ip(ip: str) -> bool:
    try:
        addr = ipaddress.ip_address(ip)
        return not (addr.is_private or addr.is_loopback or addr.is_link_local or addr.is_multicast or addr.is_reserved)
    except ValueError:
        return False


def format_row(idx: int, res: GeoResult, term: Term) -> str:
    place = ", ".join([p for p in [res.city, res.region, res.country] if p])
    org = res.org or res.isp
    ip_disp = term.cyan(term.link(res.ip, url_ipinfo(res.ip)), bold=True)
    coords_txt = f"{res.lat:>9.5f},{res.lon:>10.5f}"
    coords = term.rgb(term.link(coords_txt, url_google_maps(res.lat, res.lon)), 120, 200, 255, bold=True)
    asn = ""
    if res.asn:
        token = res.asn.strip().split()[0]
        if token.upper().startswith("AS"):
            asn = token.upper()
    asn_disp = term.violet(term.link(asn, url_bgp_asn(asn)), bold=True) if asn else ""
    src = term.gray(res.source)
    parts = [
        f"{term.gray(str(idx).rjust(3))}",
        f"{ip_disp:>39}",
        f"{term.violet(place):<32.32}",
        f"{term.neon((org or '')[:28]):<28.28}",
        f"{coords:>21}",
        f"{src}",
        f"{asn_disp}",
    ]
    return " | ".join(parts)


class LiveMapState:
    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._results: List[GeoResult] = []
        self._clients: Set["queue.Queue[str]"] = set()

    def add_result(self, res: GeoResult) -> None:
        payload = json.dumps(asdict(res), ensure_ascii=False)
        with self._lock:
            self._results.append(res)
            clients = list(self._clients)
        dead: List["queue.Queue[str]"] = []
        for q in clients:
            try:
                q.put_nowait(payload)
            except Exception:
                dead.append(q)
        if dead:
            with self._lock:
                for q in dead:
                    self._clients.discard(q)

    def snapshot(self) -> List[Dict[str, Any]]:
        with self._lock:
            return [asdict(r) for r in self._results]

    def register(self) -> "queue.Queue[str]":
        q: "queue.Queue[str]" = queue.Queue()
        with self._lock:
            self._clients.add(q)
        return q

    def unregister(self, q: "queue.Queue[str]") -> None:
        with self._lock:
            self._clients.discard(q)


MAP_HTML = """<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>IP-SCAN Live Map</title>
  <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css" />
  <style>
    html, body, #map { height: 100%; margin: 0; }
    .box {
      position: absolute;
      top: 10px;
      left: 10px;
      z-index: 1000;
      background: rgba(255,255,255,0.9);
      padding: 10px 12px;
      border-radius: 8px;
      font: 13px/1.4 system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
      max-width: 360px;
    }
    .muted { opacity: 0.7; }
    .row { margin-top: 6px; }
    code { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace; }
  </style>
</head>
<body>
  <div id="map"></div>
  <div class="box">
    <div><b>IP-SCAN</b> <span class="muted">live geolocation</span></div>
    <div class="row">Markers: <span id="count">0</span></div>
    <div class="row muted">Map data is provided by public GeoIP services.</div>
    <div class="row muted">Leave this tab open while the terminal is scanning.</div>
  </div>
  <script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
  <script>
    const map = L.map('map', { worldCopyJump: true }).setView([0, 0], 2);
    L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
      maxZoom: 19,
      attribution: '&copy; OpenStreetMap contributors'
    }).addTo(map);
    const markers = new Map();
    function setCount() {
      document.getElementById('count').textContent = String(markers.size);
    }
    function addOrUpdate(r) {
      const key = r.ip + '|' + r.lat + '|' + r.lon;
      if (markers.has(key)) return;
      const place = [r.city, r.region, r.country].filter(Boolean).join(', ');
      const org = (r.org || r.isp || '').trim();
      const title = r.ip;
      const popup = `
        <div style="min-width:220px">
          <div><b>${title}</b></div>
          <div>${place || ''}</div>
          <div class="muted">${org}</div>
          <div class="muted"><code>${r.lat.toFixed(5)}, ${r.lon.toFixed(5)}</code></div>
          <div class="muted">source: ${r.source}</div>
        </div>`;
      const m = L.marker([r.lat, r.lon], { title }).addTo(map).bindPopup(popup);
      markers.set(key, m);
      setCount();
    }
    async function loadAll() {
      const resp = await fetch('/all');
      const data = await resp.json();
      data.forEach(addOrUpdate);
      if (data.length) {
        const last = data[data.length - 1];
        map.setView([last.lat, last.lon], 5);
      }
    }
    loadAll().catch(() => {});
    const es = new EventSource('/events');
    es.onmessage = (ev) => {
      try {
        const r = JSON.parse(ev.data);
        addOrUpdate(r);
      } catch {}
    };
    es.onerror = () => {};
  </script>
</body>
</html>
"""


def make_handler(state: LiveMapState) -> Callable[..., BaseHTTPRequestHandler]:
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt: str, *args: Any) -> None:
            return

        def do_GET(self) -> None:
            if self.path == "/" or self.path.startswith("/?"):
                body = MAP_HTML.encode("utf-8")
                self.send_response(HTTPStatus.OK)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return

            if self.path == "/health":
                body = b"ok"
                self.send_response(HTTPStatus.OK)
                self.send_header("Content-Type", "text/plain; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return

            if self.path == "/all":
                body = json.dumps(state.snapshot(), ensure_ascii=False).encode("utf-8")
                self.send_response(HTTPStatus.OK)
                self.send_header("Content-Type", "application/json; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return

            if self.path == "/events":
                self.send_response(HTTPStatus.OK)
                self.send_header("Content-Type", "text/event-stream; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Connection", "keep-alive")
                self.end_headers()
                self.wfile.flush()
                q = state.register()
                try:
                    ping_at = time.time()
                    while True:
                        try:
                            msg = q.get(timeout=0.8)
                        except queue.Empty:
                            msg = ""
                        now = time.time()
                        if msg:
                            data = f"data: {msg}\n\n".encode("utf-8")
                            self.wfile.write(data)
                            self.wfile.flush()
                        elif now - ping_at >= 12.0:
                            self.wfile.write(b": ping\n\n")
                            self.wfile.flush()
                            ping_at = now
                except (ConnectionError, BrokenPipeError):
                    pass
                finally:
                    state.unregister(q)
                return

            self.send_response(HTTPStatus.NOT_FOUND)
            self.end_headers()

    return Handler


def start_map_server(host: str, port: int, state: LiveMapState) -> ThreadingHTTPServer:
    server = ThreadingHTTPServer((host, port), make_handler(state))
    t = threading.Thread(target=server.serve_forever, name="map-server", daemon=True)
    t.start()
    return server


def pick_geo_provider(name: str) -> List[Callable[[str, float], Optional[GeoResult]]]:
    providers = {
        "ip-api": geo_ip_api_com,
        "ipapi": geo_ipapi_co,
        "auto": None,
    }
    if name not in providers:
        raise ValueError(f"Unknown provider: {name}")
    if name == "auto":
        return [geo_ip_api_com, geo_ipapi_co]
    return [providers[name]]  # type: ignore[list-item]


def geolocate_ip(ip: str, timeout_s: float, provider_chain: List[Callable[[str, float], Optional[GeoResult]]]) -> Optional[GeoResult]:
    for p in provider_chain:
        try:
            res = p(ip, timeout_s)
        except (urllib.error.URLError, TimeoutError, OSError, ValueError):
            res = None
        if res is not None:
            return res
    return None


def run_scan(
    targets: List[str],
    *,
    provider: str,
    timeout_s: float,
    workers: int,
    dns_servers: List[str],
    term: Term,
    rdap: bool,
    rdap_timeout_s: float,
    http_recon: bool,
    tls_recon: bool,
    dns_extra: bool,
    max_related: int,
    interactive: bool,
    state: Optional[LiveMapState],
) -> Tuple[int, int, int]:
    provider_chain = pick_geo_provider(provider)
    to_resolve = expand_targets(targets)
    resolved: List[Tuple[str, str]] = []
    for t in to_resolve:
        if is_domain_like(t):
            host = t
            if "://" in t:
                parsed = urllib.parse.urlparse(t)
                host = parsed.hostname or t
            info = dns_lookup_all(host, dns_servers=dns_servers, timeout_s=timeout_s)
            print_domain_info(host, info, dns_servers=dns_servers, timeout_s=timeout_s, term=term)
            related = _extract_hosts_from_dns_info(host, info)
            if related:
                print(term.tag("RELATED", color="cyan") + term.dim("  ") + term.gray("NS/MX/CNAME/WWW"))
                for rh in related[: max(0, int(max_related))]:
                    ips_rh = dns_lookup_ips(rh, dns_servers=dns_servers, timeout_s=timeout_s)
                    if ips_rh:
                        ip_join = ", ".join([term.cyan(term.link(ip, url_ipinfo(ip))) for ip in ips_rh])
                        rh_disp = term.violet(term.link(rh, url_whois_domain(rh)), bold=True) if looks_like_domain(rh) else term.violet(rh, bold=True)
                        print(f"  {term.bullet()} {rh_disp} {term.gray('->')} {ip_join}")
                        for ip in ips_rh:
                            resolved.append((rh, ip))
                    else:
                        rh_disp = term.violet(term.link(rh, url_whois_domain(rh)), bold=True) if looks_like_domain(rh) else term.violet(rh, bold=True)
                        print(f"  {term.bullet()} {rh_disp} {term.gray('->')} {term.gray('no A/AAAA')}")
            if dns_extra:
                sec = dns_security_profile(host, dns_servers=dns_servers, timeout_s=timeout_s)
                if sec:
                    print(term.tag("DNS-EXTRA", color="violet") + term.dim("  ") + term.gray("email/security"))
                    for k in ["DMARC", "MTA-STS", "TLS-RPT"]:
                        vals = sec.get(k)
                        if not vals:
                            continue
                        print(term.violet(k, bold=True) + term.gray(":"))
                        for v in vals[:6]:
                            print(f"  {term.bullet()} {term.gray(v)}")
                extras = []
                for hn in [f"autodiscover.{host}", f"mail.{host}"]:
                    ips_e = dns_lookup_ips(hn, dns_servers=dns_servers, timeout_s=timeout_s)
                    if ips_e:
                        extras.append((hn, ips_e))
                if extras:
                    print(term.tag("HOSTS", color="cyan") + term.dim("  ") + term.gray("autodiscover/mail"))
                    for hn, ips_e in extras:
                        ip_join = ", ".join([term.cyan(term.link(ip, url_ipinfo(ip))) for ip in ips_e])
                        hn_disp = term.violet(term.link(hn, url_whois_domain(hn)), bold=True) if looks_like_domain(hn) else term.violet(hn, bold=True)
                        print(f"  {term.bullet()} {hn_disp} {term.gray('->')} {ip_join}")
                        for ip in ips_e:
                            resolved.append((hn, ip))
            if http_recon:
                http_data = http_probe(host, timeout_s=timeout_s)
                tls_data = tls_probe(host, timeout_s=timeout_s) if tls_recon else None
                print_http_block(host, http_data, tls_data, term)
            ips = info.get("A", []) + info.get("AAAA", [])
            if not ips:
                _, ips2 = resolve_target(t)
                ips = ips2
            for ip in ips:
                resolved.append((host, ip))
        else:
            original, ips = resolve_target(t)
            for ip in ips:
                resolved.append((original, ip))
    seen: Set[str] = set()
    tasks: List[Tuple[str, str]] = []
    for original, ip in resolved:
        if ip in seen:
            continue
        seen.add(ip)
        tasks.append((original, ip))

    total = len(tasks)
    if total == 0:
        print(term.warn("Tidak ada IP yang bisa di-resolve dari target."))
        return 0, 0, 0

    ok = 0
    skipped = 0
    failed = 0

    print("")
    print(term.tag("SCAN", color="green") + term.dim("  ") + term.gray("target IP unik = ") + term.neon(str(total)))
    width = _terminal_width()
    rule = term.rule()
    header = [
        term.gray("IDX"),
        term.cyan("IP", bold=True),
        term.violet("LOKASI", bold=True),
        term.neon("ORG/ISP"),
        term.rgb("KOORDINAT (klik)", 120, 200, 255, bold=True),
        term.gray("PROVIDER"),
        term.violet("ASN", bold=True),
    ]
    print(" | ".join(header))
    print(rule)

    def worker(original_ip: Tuple[str, str]) -> Tuple[str, str, Optional[GeoResult], str, Optional[Tuple[str, Dict[str, Any]]]]:
        original, ip = original_ip
        if not is_public_ip(ip):
            return original, ip, None, "private", None
        res = geolocate_ip(ip, timeout_s, provider_chain)
        rd: Optional[Tuple[str, Dict[str, Any]]] = None
        if rdap and res is not None:
            rdap_url, rdap_data = rdap_lookup_ip(ip, timeout_s=rdap_timeout_s)
            if rdap_url and rdap_data:
                rd = (rdap_url, rdap_data)
        return original, ip, res, "ok" if res else "fail", rd

    with ThreadPoolExecutor(max_workers=max(1, workers)) as ex:
        futs = [ex.submit(worker, t) for t in tasks]
        results: List[GeoResult] = []
        rdap_urls: Dict[str, str] = {}
        rdap_net_seen: Dict[Tuple[str, str, str, str], int] = {}
        for fut in as_completed(futs):
            original, ip, res, status, rd = fut.result()
            if status == "private":
                skipped += 1
                continue
            if res is None:
                failed += 1
                continue
            ok += 1
            res = GeoResult(**{**asdict(res), "input": original})
            results.append(res)
            print(format_row(len(results), res, term))
            if rd is not None:
                rdap_url, rdap_data = rd
                rdap_urls[ip] = rdap_url
                try:
                    summary = rdap_summarize_ip(rdap_data)
                    net_key = (
                        str(summary.get("NetHandle") or ""),
                        str(summary.get("CIDR") or summary.get("NetRange") or ""),
                        str(summary.get("OrgId") or ""),
                        str(summary.get("NetName") or ""),
                    )
                    first_idx = rdap_net_seen.get(net_key)
                    if first_idx is None:
                        rdap_net_seen[net_key] = len(results)
                        print_rdap_block(len(results), ip, rdap_url, summary, term)
                    else:
                        netname = str(summary.get("NetName") or "").strip()
                        cidr = str(summary.get("CIDR") or "").strip()
                        hint = " ".join([p for p in [netname, cidr] if p]).strip()
                        line = term.dim("  ") + term.tag("RDAP", color="violet") + term.dim("  ") + term.cyan(term.link(ip, rdap_url), bold=True)
                        line += term.gray("  = same-net #") + term.neon(str(first_idx))
                        if hint:
                            line += term.gray(" :: ") + term.gray(_truncate_middle(hint, 80))
                        print(line)
                except Exception:
                    pass
            if state is not None:
                state.add_result(res)

    print(rule)
    print(term.ok(f"Sukses: {ok}") + term.dim(" | ") + term.bad(f"Gagal: {failed}") + term.dim(" | ") + term.warn(f"Skip(private): {skipped}"))

    orgs = [(r.org or r.isp or "").strip() for r in results]
    countries = [r.country.strip() for r in results if r.country.strip()]
    asns: List[str] = []
    for r in results:
        if not r.asn:
            continue
        token = r.asn.strip().split()[0].upper()
        if token.startswith("AS"):
            asns.append(token)

    if results:
        print("")
        print(term.tag("SUMMARY", color="cyan") + term.dim("  ") + term.gray("ringkas"))
        top_org = _top_counts(orgs, 4)
        top_cc = _top_counts(countries, 4)
        top_asn = _top_counts(asns, 6)
        if top_org:
            s = ", ".join([f"{name}({cnt})" for name, cnt in top_org])
            print(f"  {term.bullet()} {term.gray('org:')} {term.neon(s)}")
        if top_cc:
            s = ", ".join([f"{name}({cnt})" for name, cnt in top_cc])
            print(f"  {term.bullet()} {term.gray('country:')} {term.violet(s)}")
        if top_asn:
            s = ", ".join([f"{name}({cnt})" for name, cnt in top_asn])
            print(f"  {term.bullet()} {term.gray('asn:')} {term.cyan(s)}")

    if interactive and results and sys.stdin is not None and sys.stdin.isatty():
        print("")
        print(term.dim("Klik link di terminal (jika support). Atau pakai command interaktif:"))
        print(term.dim("  open <idx> map|osm|ip|whois|asn|rdap   |  list  |  quit"))
        while True:
            try:
                cmd = input(term.dim("ip-scan> ")).strip()
            except (EOFError, KeyboardInterrupt):
                print("")
                break
            if not cmd:
                continue
            low = cmd.lower()
            if low in ("q", "quit", "exit"):
                break
            if low in ("l", "list"):
                for i, r in enumerate(results, start=1):
                    ip_disp = term.link(r.ip, url_ipinfo(r.ip))
                    place = ", ".join([p for p in [r.city, r.region, r.country] if p])
                    coords = term.link(f"{r.lat:.5f},{r.lon:.5f}", url_google_maps(r.lat, r.lon))
                    print(f"{term.dim(str(i).rjust(3))} {ip_disp} {term.dim('|')} {place} {term.dim('|')} {coords}")
                continue
            parts = cmd.split()
            if len(parts) >= 2 and parts[0].lower() == "open":
                try:
                    idx = int(parts[1])
                except ValueError:
                    print(term.warn("IDX harus angka."))
                    continue
                if idx < 1 or idx > len(results):
                    print(term.warn("IDX di luar range."))
                    continue
                target = results[idx - 1]
                action = (parts[2].lower() if len(parts) >= 3 else "map").strip()
                url = ""
                if action in ("map", "gmaps", "google"):
                    url = url_google_maps(target.lat, target.lon)
                elif action in ("osm", "openstreetmap"):
                    url = url_openstreetmap(target.lat, target.lon)
                elif action in ("ip", "ipinfo"):
                    url = url_ipinfo(target.ip)
                elif action in ("whois",):
                    url = url_whois_ip(target.ip)
                elif action in ("asn",):
                    if target.asn:
                        token = target.asn.strip().split()[0].upper()
                        if token.startswith("AS"):
                            url = url_bgp_asn(token)
                elif action in ("rdap",):
                    url = rdap_urls.get(target.ip, "")
                    if not url:
                        url = f"https://rdap.arin.net/registry/ip/{urllib.parse.quote(target.ip)}"
                if not url:
                    print(term.warn("Aksi tidak dikenal atau data tidak tersedia."))
                    continue
                try:
                    webbrowser.open(url, new=2)
                    print(term.ok("OPEN") + term.dim(" :: ") + url)
                except Exception:
                    print(term.warn("Gagal membuka browser."))
                continue
            print(term.warn("Command tidak dikenal. Gunakan: open <idx> map|osm|ip|whois|asn"))
    return total, ok, failed


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="ip_scan.py",
        description="Scan domain/IP, resolve DNS, GeoIP lookup, dan tampilkan marker real-time di peta (Leaflet).",
    )
    p.add_argument("targets", nargs="*", help="Target domain/IP/URL/CIDR (contoh: example.com, 8.8.8.8, 1.1.1.0/24)")
    p.add_argument("-f", "--file", help="File berisi daftar target (satu per baris)")
    p.add_argument("--provider", choices=["auto", "ip-api", "ipapi"], default="auto", help="Pilih GeoIP provider (default: auto/fallback)")
    p.add_argument("--timeout", type=float, default=6.0, help="Timeout request GeoIP (detik)")
    p.add_argument("-w", "--workers", type=int, default=12, help="Jumlah worker paralel untuk lookup")
    p.add_argument("--dns", default="1.1.1.1,8.8.8.8", help="DNS server (comma-separated). Default: 1.1.1.1,8.8.8.8")
    p.add_argument("--rdap", action="store_true", help="Tampilkan output IP WHOIS via RDAP (lebih lengkap)")
    p.add_argument("--rdap-timeout", type=float, default=8.0, help="Timeout request RDAP (detik)")
    p.add_argument("--no-auto-rdap", action="store_true", help="Matikan auto-RDAP saat scan domain (default: aktif untuk 1 target domain)")
    p.add_argument("--dns-extra", action="store_true", help="Tambah cek DNS tambahan (DMARC/MTA-STS/TLS-RPT, dll)")
    p.add_argument("--http", action="store_true", help="Tambah recon HTTP (status, redirect, headers, title)")
    p.add_argument("--tls", action="store_true", help="Tambah recon TLS cert (butuh --http atau scan domain)")
    p.add_argument("--max-related", type=int, default=20, help="Batas host RELATED yang di-resolve (default: 20)")
    p.add_argument("--full", action="store_true", help="Mode lengkap (setara: --rdap --menu)")
    p.add_argument("--no-color", action="store_true", help="Matikan warna output")
    p.add_argument("--no-links", action="store_true", help="Matikan link klik (OSC 8)")
    p.add_argument("--force-color", action="store_true", help="Paksa warna output meski bukan TTY")
    p.add_argument("--force-links", action="store_true", help="Paksa link klik (OSC 8) meski bukan TTY")
    p.add_argument("--menu", action="store_true", help="Aktifkan mode interaktif setelah scan")
    p.add_argument("--map", action="store_true", help="Aktifkan live map (server lokal + browser)")
    p.add_argument("--host", default="127.0.0.1", help="Host server map (default: 127.0.0.1)")
    p.add_argument("--port", type=int, default=8000, help="Port server map (default: 8000)")
    p.add_argument("--no-browser", action="store_true", help="Jangan auto-buka browser")
    p.add_argument("--keep", action="store_true", help="Tetap hidup setelah scan selesai (untuk lihat map)")
    return p


def main() -> int:
    args = build_parser().parse_args()
    force_color = bool(args.force_color) or bool(os.environ.get("FORCE_COLOR"))
    force_links = bool(args.force_links) or bool(os.environ.get("FORCE_LINKS"))
    is_tty = bool(sys.stdout.isatty())
    color_on = (not bool(args.no_color)) and (is_tty or force_color)
    links_on = (not bool(args.no_links)) and (is_tty or force_links)
    term = Term(color=color_on, links=links_on)
    print(term.gray("By Nofri.Flory"))
    targets = list(args.targets)
    if args.file:
        try:
            targets.extend(read_targets_from_file(args.file))
        except OSError as e:
            print(term.bad("Gagal baca file: ") + str(e))
            return 2

    targets = [t for t in targets if t.strip()]
    if not targets:
        if sys.stdin is not None and sys.stdin.isatty():
            try:
                one = input("Masukkan domain atau IP: ").strip()
            except EOFError:
                one = ""
            if one:
                targets = [one]
            else:
                print(term.warn("Input kosong. Contoh: google.com atau 8.8.8.8"))
                return 2
        else:
            print(term.warn("Masukkan target domain/IP atau pakai -f targets.txt"))
            return 2

    state: Optional[LiveMapState] = None
    server: Optional[ThreadingHTTPServer] = None
    if args.map:
        state = LiveMapState()
        try:
            server = start_map_server(args.host, args.port, state)
        except OSError as e:
            print(term.bad(f"Gagal start map server {args.host}:{args.port}: ") + str(e))
            return 2
        url = f"http://{args.host}:{args.port}/"
        print(term.info("LIVE MAP") + term.dim(" :: ") + term.link(url, url))
        if not args.no_browser:
            try:
                webbrowser.open(url, new=2)
            except Exception:
                pass

    try:
        dns_servers = [s.strip() for s in str(args.dns).split(",") if s.strip()]
        if not dns_servers:
            dns_servers = ["1.1.1.1", "8.8.8.8"]
        auto_rdap = (not bool(args.no_auto_rdap)) and len(targets) == 1 and is_domain_like(targets[0])
        full_on = bool(args.full)
        rdap_on = bool(args.rdap) or full_on or auto_rdap
        menu_on = bool(args.menu) or full_on
        dns_extra_on = bool(args.dns_extra) or full_on
        http_on = bool(args.http) or full_on
        tls_on = bool(args.tls) or full_on
        run_scan(
            targets,
            provider=args.provider,
            timeout_s=float(args.timeout),
            workers=int(args.workers),
            dns_servers=dns_servers,
            term=term,
            rdap=rdap_on,
            rdap_timeout_s=float(args.rdap_timeout),
            http_recon=http_on,
            tls_recon=tls_on,
            dns_extra=dns_extra_on,
            max_related=int(args.max_related),
            interactive=menu_on,
            state=state,
        )
    except KeyboardInterrupt:
        print("\n" + term.warn("Dibatalkan."))
    finally:
        if server is not None and not args.keep:
            server.shutdown()
            server.server_close()
    if server is not None and args.keep:
        try:
            while True:
                time.sleep(0.5)
        except KeyboardInterrupt:
            server.shutdown()
            server.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
