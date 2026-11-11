# 文献の属性 `@[cite …]` と略号（設計と一括レーンの計画）

作成：2026-11-11（段階 II の調整役）。決定：ユーザー（11-11、「属性まで、上の例で、KL-W1 の後の一括で ok」）。

## 1. 目的

宣言と文献の番号の対応を、docstring の地の文だけでなく、Lean の環境から引けるようにする。文献ごとの地図（HTT・HA・Prisms・Kerodon・K）は、手で書いた「名前 @ パス:行」をやめて、属性から作る。docstring にも、今までどおり番号を文章で書く（属性は機械のため、文章は人のため）。

## 2. 属性

- Kerodon と Stacks は Mathlib の `@[kerodon TAG]`・`@[stacks TAG]` を使う（Mathlib `Tactic/StacksAttribute`）。
- それ以外の文献は、同じ作りの `@[cite KEY "番号"]` を本体に置く。例：`@[cite HTT "5.5.2.9"]`、`@[cite BS19 "Prop 7.10"]`。照会のコマンド（`#cite_tags KEY` のように、番号・宣言・モジュール・行を出すもの）も置く。Mathlib の作りを手本にする。
- partial の対応には種類を付けられるようにする（`special`・`direction`・`stronger-hyp`・`component`、Kerodon の確認 §8.1 の基準）。書き方は実装のときに決める。

## 3. 略号と版

| 略号 | 文献 | 版 |
| --- | --- | --- |
| BS19 | Bhatt–Scholze, Prisms and prismatic cohomology | 著者版（`paper/refs/BS-prisms-author.pdf`） |
| BS17 | Bhatt–Scholze, Projectivity of the Witt vector affine Grassmannian | arXiv:1507.06490 |
| HTT | Lurie, Higher Topos Theory | 2017-04-09 版 |
| HA | Lurie, Higher Algebra | 2017-09-18 版 |
| Kerodon | Lurie, Kerodon | Tag（Mathlib の属性） |
| Stacks | The Stacks project | Tag（Mathlib の属性） |
| LT | Land–Tamme | 引用している版を README に書く |
| KST | Kerz–Strunk–Tamme | 同上 |
| BGT | Blumberg–Gepner–Tabuada | 同上 |
| TT | Thomason–Trobaugh | 同上 |
| BST13 | Bhatt–Schnell–Scholze | arXiv:1307.3763 |
| Rydh | Rydh, Submersions and effective descent | arXiv:0710.2488 |

一覧は README の「Conventions」にも置き、文献が増えたら足す。

## 4. 時期と一括レーン

1. KL-W1 の停止点 3 の取り込み → 対応表の宣言の場所の書き直し（coordination.md の暦）。
2. その後に一括レーンを開く。属性と照会のコマンドの実装、README の略号表、既存の対応表（HTT 896 件、HA 645 件、Prisms 287 件、K の地図）の own・partial から属性を自動で付ける。多くのファイルを書き換えるので、夜の bulk として流す。
3. 付け終わったら、地図を属性から作り直す。
4. 以後、すべての指示書の規則に「新しい宣言には文献の属性を付ける」を足す。
