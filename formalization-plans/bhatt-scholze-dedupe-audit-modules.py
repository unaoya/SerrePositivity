# 専用監査の `let <名前> : Array Name := #[ ... ]` から、統合で同じ名前になった重複行を除く（BS-W8）。
import re, sys, pathlib
for f in sys.argv[1:]:
    p = pathlib.Path(f); s = p.read_text()
    def fix(m):
        names = re.findall(r"`[\w.']+", m.group(2))
        uniq = list(dict.fromkeys(names))
        return m.group(1) + (",\n    ".join(uniq)) + "]"
    s2, k = re.subn(r"(let \w+ : Array Name := #\[\s*)((?:`[\w.']+,?\s*)+)\]", fix, s)
    p.write_text(s2); print(f, k, "changed" if s2 != s else "unchanged")
