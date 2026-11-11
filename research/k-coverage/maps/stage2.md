# 停止点 2　本論文 §3–4、Tamme、BGT

照合基点は `6e19c5a14`。版は各目次に記載。Lean 4.35.0-rc4 で、対応する宣言の `#check` と `#print axioms` を共有ロック下で実行した。依存モジュールのソースと manifest を照合し、既存の olean を用いた。

| 文献 | own | mathlib | both | partial | interface | none | 計 | 凍結 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 本論文 §3–4 | 8 | 0 | 0 | 7 | 7 | 40 | 62 | 0 |
| Tamme | 9 | 0 | 0 | 10 | 0 | 31 | 50 | 0 |
| BGT | 4 | 0 | 0 | 10 | 0 | 233 | 247 | 0 |

none には主張を持たない見出しと記法を含む（本論文 11 行、Tamme 3 行、BGT 49 行）。partial は Lean の宣言から原典の結論の一部が直接従う場合に限り、`partial_kind` に分類を記録した。

- 本論文 3.1 と (3.2) の界面は離散・局所の場合の K₀ で不変類の正整数倍を持ち上げる。4.7 で用いる界面は台つきランク商の三角 K₀ 版。両方に `sorryAx` があり、3.5 の共役和と 4.7 もそれぞれの入力に依存する。(3.1) のスペクトル降下と 4.6 の連結係数代数による両 Perf の表示は確認できなかった。
- 本論文 4.2 では台つき部分商の埋め込みと Karoubi 包の比較を確認した。4.3 では非負性と K₀ の Euler 評価、4.5 では正規化長さ側の階数倍を確認した。
- Tamme の lax 引き戻しの定義、写像空間、分裂列、差の右随伴は直接対応する。15・18 は小安定圏の右脚自体に充満忠実な右随伴がある場合。原典の Ind での切除性から小圏の完全列へ降ろす一般形と、環スペクトルの Tor 単位性からの適用は確認できなかった。
- BGT 7.1 の Gap 条件は全区間四角形の条件と同値。7.3 の初項制限同値は安定準圏で確認した。9.1・9.4・9.6 の近接型には dg 円錐と懸垂塔の実余極限がある。円錐の周囲の dg 導来圏と原典の Indω の同定が残り、§9.3 の非連結 K の局所化の登録も確認できなかった。

段 1 の partial 91 行を既存の kernel 記録と原典で再判定した。KST は 7 行、Land–Tamme は 10 行を旧候補のまま partial と判定した。旧候補から原典への追加比較が必要な行と、Land–Tamme (11) と (12) の中央項の区別を別表に記録した。[段 1 の再判定](stage1-partial-review.csv)

各行の kernel 型と公理、および none の引用・概念検索・近接宣言の記録は文献ごとに分けた。

- 本論文 §3–4 [項目表](paper/items.csv) · [型と公理](paper/kernel-evidence.json) · [検索記録](paper/none-search.json) · [充満忠実性のインスタンス](paper/instance-evidence.json)
- Tamme [項目表](tamme/items.csv) · [型と公理](tamme/kernel-evidence.json) · [検索記録](tamme/none-search.json)
- BGT [項目表](bgt/items.csv) · [型と公理](bgt/kernel-evidence.json) · [検索記録](bgt/none-search.json)
