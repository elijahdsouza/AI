#!/usr/bin/env python3
"""Fold index.html and its dependencies into one openable file.

The repo already ships its landing pages as single self-contained HTML
(UC_Landing_V10_Final.html, uc-membership-landing-v19_1.html), so this
keeps to that convention. Source of truth stays index.html plus the
unmodified engine; this only packages them.

    python3 build/inline.py

Writes UC-Pro-Group-hero-directions.html next to index.html.

Fonts are still fetched from Google at runtime. For a genuinely offline
build, inline the woff2 payloads as well, the way build/inline_fonts.py
does in the v19 project.
"""
import base64
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT_NAME = "UC-Pro-Group-landing.html"

REPLACEMENTS = [
    ('<link rel="stylesheet" href="scrollcraft.css">',
     "scrollcraft.css",
     "<style>\n/* scrollcraft engine stylesheet, inlined */\n{}\n</style>"),
    ('<script src="scrollcraft.js"></script>',
     "scrollcraft.js",
     "<script>\n/* scrollcraft engine, inlined, unmodified */\n{}\n</script>"),
]

# published path -> (media type, source file)
IMAGES = {"assets/table.jpg": ("image/jpeg", "assets/table.jpg")}


def main() -> int:
    html = (ROOT / "index.html").read_text(encoding="utf-8")

    # The engine links are optional: the current page is standalone, while
    # archive/spread-v1.html still links them. Inline whatever is present.
    for needle, src, wrapper in REPLACEMENTS:
        if needle not in html:
            continue
        html = html.replace(needle, wrapper.format(
            (ROOT / src).read_text(encoding="utf-8")))

    for ref, (mime, src) in IMAGES.items():
        needle = f'src="{ref}"'
        if needle not in html:
            print(f"error: {needle!r} not found in index.html", file=sys.stderr)
            return 1
        b64 = base64.b64encode((ROOT / src).read_bytes()).decode("ascii")
        html = html.replace(needle, f'src="data:{mime};base64,{b64}"')

    leftovers = [r for r in (*IMAGES, "scrollcraft.css", "scrollcraft.js")
                 if f'"{r}"' in html]
    if leftovers:
        print(f"error: unresolved refs remain: {leftovers}", file=sys.stderr)
        return 1

    out = ROOT / OUT_NAME
    out.write_text(html, encoding="utf-8")
    print(f"wrote {out.relative_to(ROOT)}  {round(out.stat().st_size / 1024)} KB")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
