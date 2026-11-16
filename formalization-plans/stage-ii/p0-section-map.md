# P⁰ の節の地図：DAG XIII・NS の対応表と、節の閉包（紙）

作成：2026-11-16 夕（調整役）。決定：ユーザー（11-16「okです」、方針は `p0-plan-draft.md` §6）。

## 0. 目的

計画の単位は文献の節（`p0-plan-draft.md` §6）。P⁰（DAG XIII Constr 2.2.6）への依存をたどって行き当たる節を、文献ごとに項目として全部挙げ、依存の順に並べる。これが段階の計画と進み具合の物差しになる。

## 1. ⑤a：DAG XIII と NS の対応表（新設）

- 置き場所：`research/dag13-coverage/`・`research/ns-coverage/`。形は HA の対応表（`research/ha-coverage/README.md`）と同じ：`toc.md`（節・小節の見出し）、`items.csv`（列 `number,kind,title,section,status,declarations,reason,confidence,lean_citations,plan_citations,kerodon,goal`、`kerodon` の列は他文献の同じ内容の番号を `HA 6.1.6.7` のように書いてよい）、`review/` に照合の結果。
- 範囲：**論文全体**の見出しと番号つきの全項目（HA の表と同じく本全体）。照合（status・declarations・reason）は、P⁰ に至る節（DAG XIII §1.1・§2.1・§2.2、NS I.1・I.3・III.1・IV.1 など）を先に、その後に残り。
- 版：DAG XIII は 2011 年の版（段 0 の報告で照合した版）、NS は arXiv:1707.01799v2。toc.md の冒頭に記録する。
- **文献の略号の登録**：`research/bibliography.json` に `DAGXIII`・`NS` を足し、`scripts/refactor/bulk_citation_registry.py` で `SerrePositivity/Util/Citation.lean` の登録を作り直す。対象ビルド（`Util/Citation` とそれを import するもの）は共有の鍵 `--class impl` で。これだけが Lean の変更。

## 2. ⑤d：HA・HTT・Kerodon の側の節の閉包

- 出発点：DAG XIII §2.2（Constr 2.2.6 とその前提）と NS の P⁰ に関わる節が引く HA・HTT・Kerodon の番号。⑤a の対応表ができる前でも、原典から直接拾ってよい。
- たどり方：閉包に入った節について、その節の定義・主張・証明が引く番号と、節の中の項目の前提を拾い、その番号を含む節を閉包に加える。これを繰り返す。節の中は全項目を作る前提なので、一項目でも要れば節ごと入る。
- 出力：`research/p0-lurie/section-closure/sections.csv`（列 `source,section,title,reached_from,reason`。**状態・項目数の列は持たない**）と `edges.csv`（節 → 節、根拠の番号）、依存の順（トポロジカル順）の一覧 `order.md`。HA・HTT・Kerodon の項目と状態は既存の対応表（`research/ha-coverage`・`htt-coverage`・`kerodon-coverage` の review）が唯一の正本で、閉包の資料には写さない（二重管理にしない）。
- **止める条件**：閉包が 150 節を超えたら、その時点の表をコミットして報告して止まる（大きさを見て進め方を決める）。

## 3. 規則

- 紙だけ（§1 の略号の登録を除く）。Lean の追加・ビルドはしない。
- 既存の対応表（HA・HTT・Kerodon の review）は書き換えない。食い違いを見つけたら報告に書く。
- それぞれ main（0bdc68cee 以降）から枝を切り、報告をコミットしたら止まる。調整役が二つを合わせて節の一覧と HTML の地図にする。

## 4. 地図（11-16、ユーザー）

新しい地図は作らず、既存の P⁰ の地図（`research/p0-lurie/p0-map.html`、公開 https://claude.ai/artifact/9hAePSTR4easWKwT35Wtiv）を更新する。§1・§2 の結果から、節単位の表示（文献ごとの節、依存の順、節ごとの own／partial／none）と、DAG XIII・NS の全項目を足す。調整役が行う。

## 5. 正本は一つ（11-16、ユーザー）

HA・HTT・Kerodon の項目と状態は二重管理にしない。正本は既存の対応表（各 `research/<文献>-coverage/review/`、B5 の後は Lean の文献の属性から作るもの）だけ。
- 閉包の資料（§2）は節の名前と依存の辺だけを持つ。
- P⁰ の地図は手で状態を書かず、生成スクリプト（`research/p0-lurie/build_p0_map.py`、調整役が作る）で、閉包の資料と各対応表を読んで作り直す。今の 59 項目の表の状態も、HA・HTT・Kerodon の分は対応表から引く形に置き換える（BS・DAG XIII・NS の分は、それぞれの対応表 `bs-coverage`・`dag13-coverage`・`ns-coverage` から）。
- 対応表と食い違う判定を見つけたら、地図ではなく対応表の側を直す（レーンは報告に書き、調整役が対応表を直す）。地図は既存の HA・HTT・Kerodon の地図（Artifact）へ節ごとに結ぶ。

## 6. 当面の進め方（11-16 夕、ユーザー）

今の作業は進め、新しい作業は始めない。
- ⑥（2g）は対応表・地図と関係しないのでそのまま進める。一括（KL-W1 のチャット）は **5∞-3a の完成で止まる**（ユーザー決定、A6・A8 の特別な場合の決定を見直すまで 5∞-7a へ進まない）。B2・B5・B6 は対応表の更新が済むまで始めない。
- ③-a は 5∞-1 の完成（停止点）で、③-b は OE-W1 の段 1 の完成（停止点）で止まる。どちらもその先（5∞-2、OE-W1 の段 2）へは進まない。
- ⑤a・⑤d は §1・§2 の紙を続ける。
- ③-a・③-b の取り込みの後、改めて整理する：HA・HTT・Kerodon の対応表の場所を改名表で書き直し、新しいコード（11-12 以降の約 1,000 本と、取り込む 5∞-1・OE-W1）が関わる行の状態を照合し直す。そのうえで P⁰ の地図を生成スクリプトで作り直す。担当はそのときに決める。
