#!/usr/bin/env python3
"""Generate docs/assets/banner.svg and docs/assets/hero_terminal.svg from real results.

Inputs: results/tlc/*.json + *.log (scripts/run_tlc.py), results/tracecheck.json
(scripts/validate_traces.py), results/lean_build.txt (`lake build` output) and the theorem
statements in lean/OrbitProofs/*.lean. Nothing is typed in by hand: every number and every line
of "terminal output" is read from those files.
"""
from __future__ import annotations

import json
import math
import re
from html import escape
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RES = ROOT / "results"
ASSETS = ROOT / "docs" / "assets"
ACCENT = "#C084FC"
MONO = "ui-monospace,SFMono-Regular,Menlo,Consolas,monospace"


def tlc_results():
    out = {}
    for p in sorted((RES / "tlc").glob("*.json")):
        out[p.stem] = json.loads(p.read_text())
    return out


def theorems():
    names = []
    for f in sorted((ROOT / "lean" / "OrbitProofs").glob("*.lean")):
        names += re.findall(r"^theorem (\S+)", f.read_text(encoding="utf-8"), re.M)
    return names


def log_lines(name, pats):
    text = (RES / "tlc" / f"{name}.log").read_text(encoding="utf-8")
    keep = []
    for line in text.splitlines():
        if any(re.search(p, line) for p in pats):
            keep.append(line.strip())
    return keep


def banner(tlc, thms, tc):
    W, H = 1280, 400
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">',
             '<rect width="100%" height="100%" fill="#0d1117"/>',
             '<defs><pattern id="g" width="32" height="32" patternUnits="userSpaceOnUse">'
             '<path d="M32 0H0V32" fill="none" stroke="#161b22" stroke-width="1"/></pattern></defs>',
             '<rect width="100%" height="100%" fill="url(#g)"/>',
             f'<text x="64" y="170" font-family="{MONO}" font-weight="700" font-size="84" fill="#e6edf3">proofstack</text>',
             f'<text x="66" y="222" font-family="{MONO}" font-size="24" fill="#8b949e">TLA+ model checking, trace validation and Lean proofs</text>',
             f'<text x="66" y="256" font-family="{MONO}" font-size="24" fill="#8b949e">for raftstore (Raft) and orbit-os (buddy allocator, MMU)</text>']
    total_states = sum(r.get("distinct", 0) for k, r in tlc.items() if not k.startswith("mut-"))
    parts.append(f'<text x="66" y="330" font-family="{MONO}" font-size="18" fill="{ACCENT}">'
                 f'{total_states:,} distinct states  ·  {tc["total"]["traces"]} traces / '
                 f'{tc["total"]["events"]:,} events  ·  {len(thms)} Lean theorems</text>')
    # motif: distinct states per exhaustively checked model, log scale (real TLC numbers)
    models = [(k, r["distinct"]) for k, r in sorted(tlc.items(), key=lambda kv: kv[1].get("distinct", 0))
              if not k.startswith("mut-") and r.get("distinct")]
    x0, base, maxh = 900, 330, 240
    top = math.log10(max(v for _, v in models))
    bw = min(48, 300 // max(1, len(models)))
    for k, (name, v) in enumerate(models):
        h = maxh * math.log10(v) / top
        x = x0 + k * (bw + 10)
        parts.append(f'<rect x="{x}" y="{base - h:.1f}" width="{bw}" height="{h:.1f}" rx="3" fill="{ACCENT}" '
                     f'fill-opacity="{0.35 + 0.65 * (k + 1) / len(models):.2f}"/>')
        parts.append(f'<text x="{x + bw / 2:.1f}" y="{base + 18}" font-family="{MONO}" font-size="10" '
                     f'fill="#8b949e" text-anchor="middle">{escape(name.replace("xcheck-", "x-"))}</text>')
    parts.append(f'<text x="{x0}" y="{base - maxh - 14}" font-family="{MONO}" font-size="12" fill="#8b949e">'
                 'distinct states per TLC model (log scale)</text>')
    parts.append("</svg>")
    return "\n".join(parts)


def terminal(lines, title):
    lh, pad = 19, 18
    W = 1000
    H = 40 + pad * 2 + lh * len(lines)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">',
           f'<rect width="{W}" height="{H}" rx="10" fill="#0d1117" stroke="#30363d"/>',
           f'<rect width="{W}" height="32" rx="10" fill="#161b22"/><rect y="22" width="{W}" height="10" fill="#161b22"/>',
           '<circle cx="20" cy="16" r="6" fill="#f85149"/><circle cx="40" cy="16" r="6" fill="#d29922"/>'
           '<circle cx="60" cy="16" r="6" fill="#3fb950"/>',
           f'<text x="{W / 2}" y="21" font-family="{MONO}" font-size="13" fill="#8b949e" text-anchor="middle">{escape(title)}</text>']
    y = 40 + pad
    for kind, text in lines:
        color = {"cmd": "#e6edf3", "ok": "#3fb950", "bad": "#f85149", "acc": ACCENT}.get(kind, "#8b949e")
        prefix = "$ " if kind == "cmd" else "  "
        out.append(f'<text x="18" y="{y}" font-family="{MONO}" font-size="13.5" fill="{color}" xml:space="preserve">'
                   f'{escape(prefix + text)}</text>')
        y += lh
    out.append("</svg>")
    return "\n".join(out)


def hero(tlc, thms, tc):
    L = []
    cfg = (ROOT / "tla" / "models" / "core3.cfg").read_text(encoding="utf-8")
    inv = [x for x in cfg.splitlines() if x.startswith("INVARIANTS")][0]
    L.append(("cmd", "grep INVARIANTS tla/models/core3.cfg"))
    words = inv.split()
    L.append(("acc", " ".join(words[:5])))
    L.append(("acc", "           " + " ".join(words[5:])))
    for name in ("xcheck-membership", "xcheck-snapshots", "core3"):
        if name not in tlc:
            continue
        L.append(("cmd", f"python scripts/run_tlc.py {name}"))
        for line in log_lines(name, [r"Model checking completed", r"states generated, .* distinct",
                                     r"depth of the complete state graph"]):
            L.append(("ok" if "No error" in line else "out", line))
    for name in ("mut-figure8", "mut-vote-any-log"):
        if name in tlc and tlc[name].get("violated"):
            L.append(("cmd", f"python scripts/run_tlc.py {name}      # deliberately broken variant"))
            L.append(("bad", f"Error: Invariant {tlc[name]['violated']} is violated."))
            last_state = [x for x in log_lines(name, [r"^State \d+:"])][-1]
            L.append(("out", last_state))
    t = tc["total"]
    L.append(("cmd", "python scripts/validate_traces.py --sim traces/sim --cluster traces/cluster"))
    # exactly what validate_traces.py printed for this summary
    L.append(("ok", json.dumps({"traces": t["traces"], "ok": t["ok"], "events": t["events"],
                                "failures": len(tc["failures"]), "seconds": tc["seconds"]})))
    lb = RES / "lean_build.txt"
    if lb.exists():
        last = [x for x in lb.read_text(encoding="utf-8").splitlines() if "Build completed" in x][-1]
        L.append(("cmd", "cd lean && lake build"))
        L.append(("ok", last.strip()))
        L.append(("cmd", "grep -c '^theorem' OrbitProofs/*.lean; grep -c sorry OrbitProofs/*.lean"))
        files = sorted((ROOT / "lean" / "OrbitProofs").glob("*.lean"))
        for pat in (r"^theorem", r"sorry"):          # exactly the two grep -c outputs, one file per line
            for f in files:
                n = len(re.findall(pat, f.read_text(encoding="utf-8"), re.M))
                L.append(("out", f"OrbitProofs/{f.name}:{n}"))
    return terminal(L, f"proofstack — real output ({tc['machine']}, {tc['date']})")


def main():
    tlc = tlc_results()
    thms = theorems()
    tc = json.loads((RES / "tracecheck.json").read_text())
    ASSETS.mkdir(parents=True, exist_ok=True)
    (ASSETS / "banner.svg").write_text(banner(tlc, thms, tc), encoding="utf-8", newline="\n")
    (ASSETS / "hero_terminal.svg").write_text(hero(tlc, thms, tc), encoding="utf-8", newline="\n")
    print("wrote", ASSETS / "banner.svg", ASSETS / "hero_terminal.svg")


if __name__ == "__main__":
    main()
