# CLMST：採用版と見出し

Cai–Lee–Ma–Schwede–Tucker, *Perfectoid signature, perfectoid Hilbert–Kunz multiplicity, and an application to local fundamental groups*。
採用版は **arXiv:2209.04046v4 [math.AC], 3 Jul 2025**（表紙の版表示）。

- 読み取り元：`../SerrePositivity/paper/refs/CLMST-2209.04046v4.pdf`。複写・変更していない。
- SHA-256：`0001a9a56839319b5d36c79fcd0dedc9dd66ac0b38029773d923fa4037f944fa`
- 大きさ：1,174,440 bytes、88 pages、PDF 1.5、612 × 792 pt。
- PDF ページと印刷ページは一致する。位置 `layout L<n>` は `pdftotext -layout` の出力を改行 LF で数える（form feed を別の改行として数えない）。外部証拠の `CLMST-layout.txt` に固定した。
- 論文本文は pp.2–82、References は pp.82–88。目次は pp.1–2。

## 全節見出し（目次順）

| 節 | 原典見出し | PDF p. |
|---|---|---:|
| 1 | Introduction | 2 |
| 2 | Preliminaries | 7 |
| 2.1 | Pure maps, split maps, and trace | 8 |
| 2.2 | Normalized length | 10 |
| 2.3 | Derived completion and flatness | 12 |
| 2.4 | Perfectoid rings and perfectoidization | 14 |
| 2.5 | Big Cohen-Macaulay algebras | 20 |
| 3 | F-signature and Hilbert-Kunz multiplicity via perfection in positive characteristic | 22 |
| 4 | Perfectoid signature and perfectoid Hilbert-Kunz multiplicity | 26 |
| 4.1 | Characterization of regular local rings | 39 |
| 5 | BCM-regularity via perfectoid signature | 43 |
| 5.1 | BCM-regular rings | 43 |
| 5.2 | BCM regularity and perfectoid signature | 48 |
| 5.3 | Strong BCM-regularity | 51 |
| 5.4 | BCM-rational rings and perfectoid rational and relative rational signatures | 54 |
| 6 | Transformation rules under finite maps | 60 |
| 6.1 | Almost projective and almost finite free modules | 63 |
| 6.2 | Transformation rule: the quasi-étale case | 66 |
| 6.3 | Transformation rule: a more general case | 69 |
| 7 | Applications | 72 |
| 8 | Further directions and questions | 80 |
| — | References | 82 |

番号なしの独立した小見出し：§1 の **Acknowledgements**（p.7）。§8 の **The choice of x and A ⊆ R**（p.80）、**More general residue fields**（p.81）、**Localization, faithfully flat extension, and semi-continuity**（p.81）、**Perfectoid signature of pairs**（p.81、本文は p.82 へ続く）。Proof / Proof of Claim 等の証明開始表示は節見出しには数えない。

## 項目番号の採用

導入の Theorem A–G はそれぞれ独立した行とし、本文の対応番号との引用辺を持たせる。
§2–7 の三段番号、§8 の二段番号、Claim・Caution・Convention・Conjecture・Question をすべて含める。
(a)・(b)、(1)–(4) 等の親項目内の小分けは原典番号を増やさず、親項目の reason に範囲を記す。

式は左欄に印刷された4段番号16件と、導入の記号ラベル `(*)` 1件の計17件を採用する。`(3.0.0.1)` は §3 の準備段落、`(6.0.1.1)` は §6.2 の Theorem 6.0.1 の後置証明にある。PDF 内部リンク名 `equation.1.0.0.1` は印刷上 `(*)`、`equation.6.2.2.1` は印刷上 `(6.0.1.1)` である。番号の桁から掲載位置を推測しない。`[ČS24, Paragraph after (2.1.3.1)]` の `(2.1.3.1)` は外部文献の位置であり、CLMST の式目録には加えない。

## 外部引用の番号・版

`edges.csv` の external は `research/bibliography.json` に同じ文献の略号があればそれを使い、なければ原典の参考文献ラベルを保つ。採用した改名は **Sta → Stacks、BS22 → BS19**。`evidence_location` の角括弧内には常に原典の引用を保持する。

特に **CLMST の [BS22] の定理番号は刊行版の番号**であり、登録済み BS19 の著者版の番号と一致するという意味ではない。たとえば CLMST `[BS22, Theorem 10.9]` と、本体が実装する著者版の番号は版をまたいで自動照合しない。辺のラベルに原典の位置を残し、既存の BS 対応表は変更していない。参考文献の同著者というだけで別文献を同じ略号へ統合しない。
