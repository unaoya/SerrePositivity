"""ブループリントの入口 SerreBlueprint/Blueprint.lean を、各部の生成結果（generated.json）から組み立てる（2026-11-18）。
使い方（root で、各部の生成の後）：python3 blueprint/scripts/gen_blueprint.py
部の見出しの tag は part-… に揃える（目次の見た目 serre.css が部を見分ける）。"""
import json, re, os, csv, glob, collections
B = 'blueprint/SerreBlueprint'
parts = []   # (tag, 題, [モジュール], 集計の一行)
def line(c):
    order = [('own', '本体'), ('mathlib', 'Mathlib'), ('both', '両方'), ('partial', '一部'), ('interface', '未証明の入力に依存'), ('none', 'なし')]
    n = sum(c.get(k, 0) for k, _ in order)
    return f'{n} 項目（' + '、'.join(f'{ja} {c[k]}' for k, ja in order if c.get(k)) + '）'
def review_counts(pattern, col):
    c = collections.Counter()
    for f in glob.glob(pattern):
        for r in csv.DictReader(open(f, encoding='utf-8')): c[r.get(col) or 'none'] += 1
    return c
p = json.load(open(f'{B}/Paper/paper-generated.json'))
parts.append(('part-paper', '本論文', [f'Paper.{m}' for m in p['modules']], line(review_counts('research/paper-coverage/review/ch*.csv', 'status'))))
for key in ['clmst', 'bs', 'vdescent']:
    d = [x for x in glob.glob(f'{B}/*/generated.json') if json.load(open(x))['key'] == key]
    if not d: continue
    g = json.load(open(d[0]))
    parts.append((f'part-{key}', g['title'], [f"{g['dir']}.{m}" for m in g['modules']], line(g['stats'])))
ktitle = {}
for l in open('research/kerodon-coverage/toc.md', encoding='utf-8'):
    m = re.match(r'- Chapter (\d+) \[[0-9A-Z]{4}\] (.*)$', l.strip())
    if m: ktitle[m.group(1)] = m.group(2).replace('$\\infty $', '∞').replace('$\\infty$', '∞')
for ch in range(1, 11):
    f = f'{B}/Kerodon/ch{ch}-generated.json'
    if not os.path.exists(f): continue
    g = json.load(open(f))
    parts.append((f'part-kerodon-{ch}', f'Kerodon 第 {ch} 章 {ktitle.get(str(ch), "")}', [f'Kerodon.{m}' for m in g['modules']],
                  line(review_counts(f'research/kerodon-coverage/review/ch{ch}.csv', 'status_new'))))
out = ['import Verso', 'import VersoManual', 'import VersoBlueprint', 'import VersoBlueprint.Commands.Graph', 'import VersoBlueprint.Commands.Summary']
out += [f'import SerreBlueprint.{m}' for _, _, ms, _ in parts for m in ms]
out += ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '',
        '#doc (Manual) "SerrePositivity ブループリント" =>', '%%%', 'tag := "serre-blueprint"', '%%%', '',
        '本論文（OpenAI, Positivity of Serre\'s Intersection Multiplicity, 2026-09-23）と、本論文と本体が使う文献の項目ごとに、SerrePositivity と Mathlib の対応する Lean の宣言を結んだブループリント。',
        '各ノードの本文は対応表（`research/` の各 `-coverage`）の照合の理由（日本語の要約）と解説の原稿で、原典の本文の写しではない。',
        '各ノードの頭の「主張」は原典の主張の要約（`statements.csv`）、その下は対応表の照合の理由。対応表の状態が「なし」でない項目は Lean の宣言に結ぶ。一部（原典どおりではない）・未証明の入力に依存するものは、カードの札と依存グラフの色で見分ける。',
        '章のファイルと、この入口は `blueprint/scripts/` の生成器が対応表から作る。手で直さない。', '',
        '*部ごとの目標と状態*', '']
GOALS = {'part-paper': '主定理（Theorem 1.1、Serre の交点重複度の正値性）。',
         'part-clmst': '本論文が使う正規化長と perfectoid の重複度の結果（§2.2 ほか）。',
         'part-bs': '本論文と CLMST が使う perfectoid 化（§7・§8）と、その土台の δ 環・prism（§2・§3）。',
         'part-vdescent': 'BS17 Theorem 4.1 (i) と BM18 Proposition 4.8（BS Proposition 8.10 の arc 層性の入力）。',
         'part-kerodon': '∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。'}
out += [f'- {t}：' + GOALS.get(tag if not tag.startswith('part-kerodon') else 'part-kerodon', '') + f'{s}' for tag, t, _, s in parts] + ['']
for tag, t, ms, _ in parts:
    out += [f'# {t}', '%%%', 'number := false', f'tag := "{tag}"', '%%%', ''] + [f'{{include 1 SerreBlueprint.{m}}}' for m in ms] + ['']
out += ['{blueprint_graph}', '{blueprint_summary}', '']
open(f'{B}/Blueprint.lean', 'w', encoding='utf-8').write('\n'.join(out))
print(len(parts), 'parts,', sum(len(ms) for _, _, ms, _ in parts), 'modules')
