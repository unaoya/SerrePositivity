#!/usr/bin/env python3
"""git の外に置いた検証の証拠の目録（manifest.json）を作る。

使い方: python3 scripts/docs/evidence_manifest.py <証拠のディレクトリ> <出力 manifest.json> [--commit HEAD] [--made-by 手順] [--note 一行]
  証拠のディレクトリ（例 ~/serre-evidence/<レーン>/<段>/）を歩き、各ファイルの相対パス・sha256・大きさを記録する。
  出力はリポジトリの evidence/<レーン>/<段>/manifest.json に置き、報告には目録のパスと commit を書く（evidence/README.md）。
"""
import argparse
import hashlib
import json
import pathlib


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("directory")
    ap.add_argument("output")
    ap.add_argument("--commit", default="", help="対象の枝の HEAD")
    ap.add_argument("--made-by", default="", help="作った手順かスクリプトのパス")
    ap.add_argument("--note", default="")
    args = ap.parse_args()
    root = pathlib.Path(args.directory).expanduser().resolve()
    files = []
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        h = hashlib.sha256()
        with path.open("rb") as f:
            for chunk in iter(lambda: f.read(1 << 20), b""):
                h.update(chunk)
        files.append({"path": path.relative_to(root).as_posix(), "sha256": h.hexdigest(), "bytes": path.stat().st_size})
    manifest = {"directory": str(root), "commit": args.commit, "made_by": args.made_by, "note": args.note,
                "files": files, "total_bytes": sum(f["bytes"] for f in files)}
    out = pathlib.Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(manifest, ensure_ascii=False, indent=1) + "\n")
    print(f"{len(files)} files, {manifest['total_bytes']} bytes -> {out}")


if __name__ == "__main__":
    main()
