"""原稿（research/<文献>-coverage/notes/<番号>.md）を Verso の本文に変える。gen_kerodon.py・gen_paper.py が使う。

Markdown → Verso：HTML コメントと追跡用 <a id> を落とし、## 見出しは太字の段落に、\\( \\)・\\[ \\]（複数行も）は Verso の数式
$`…`・$$`…` に、**太字** は *太字* に、pipe table は箇条書きに、リンクは表示文言だけに。冒頭の題と、ノードの頭と重なる行
（skip で渡す接頭辞）は落とす。"""
import re, os, html

def esc(s):
    return re.sub(r'([\\*_`\[\]{}#$<>|~^])', r'\\\1', s)

def esc_text(s):
    s = re.sub(r'\[([^\]]*)\]\([^)]*\)', r'\1', s)
    parts = re.split(r'(\\\(.+?\\\)|\\\[.+?\\\])', s)
    out = []
    for p in parts:
        if p.startswith('\\(') and p.endswith('\\)'): out.append('$`' + p[2:-2].strip().replace('`', "'") + '`')
        elif p.startswith('\\[') and p.endswith('\\]'): out.append('$$`' + p[2:-2].strip().replace('`', "'") + '`')
        else:
            p = html.unescape(p)
            # **太字** → *太字*（Verso）。対になっているものだけ。
            segs = re.split(r'\*\*(\S(?:.*?\S)?)\*\*', p)
            out.append(''.join(esc(x) if i % 2 == 0 else '*' + esc(x) + '*' for i, x in enumerate(segs)))
    return ''.join(out)

def note_body(fp, skip=()):
    if not os.path.exists(fp): return None
    text = open(fp, encoding='utf-8').read()
    # 複数行の \[ … \] は一行に
    text = re.sub(r'\\\[(.+?)\\\]', lambda m: '\\[' + ' '.join(m.group(1).split()) + '\\]', text, flags=re.S)
    out = []
    for s in text.split('\n'):
        if s.startswith('# ') or s.startswith('<!--') or s.startswith('<a id=') or any(s.startswith(k) for k in skip): continue
        if s.startswith('## '): out.append('*' + esc_text(s[3:].strip()).replace('*', '') + '*\n'); continue
        if s.startswith('|'):
            cells = [c.strip() for c in s.strip().strip('|').split('|')]
            if all(re.fullmatch(r':?-+:?', c) for c in cells if c): continue
            out.append('- ' + '　／　'.join(esc_text(c) for c in cells)); continue
        out.append(esc_text(s))
    text = re.sub(r'\n{3,}', '\n\n', '\n'.join(out)).strip('\n')
    return text + '\n' if text else None

def statements(P):
    """research/<文献>-coverage/statements.csv（number,statement_ja）を {番号: Verso の一段落} に（NB-W4、11-18）。"""
    import csv
    fp = f'{P}/statements.csv'
    if not os.path.exists(fp): return {}
    return {r['number']: '*主張*　' + esc_text(r['statement_ja'].strip()) + '\n'
            for r in csv.DictReader(open(fp, encoding='utf-8')) if r.get('statement_ja', '').strip()}
