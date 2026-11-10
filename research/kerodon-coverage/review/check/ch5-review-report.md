# Ch 5 対応表確認結果（2026-11-07 JST）

対象は items.csv の Ch 5 全 345 項目。結果は [章 CSV](../ch5.csv)。確認用の Lean コマンドは既存宣言の型・公理・instance を調べるものに限った。

判定は ok 191 件、fix 154 件、unsure 0 件。check は found 13 件、renamed 151 件、not_found 181 件。

## 判定の内訳

| 元の status | ok | fix | unsure |
| --- | ---: | ---: | ---: |
| own | 0 | 62 | 0 |
| mathlib | 6 | 0 | 0 |
| both | 0 | 1 | 0 |
| partial | 7 | 85 | 0 |
| none | 178 | 6 | 0 |

| 優先理由 | 対象 | fix | fix の率 | status 訂正 | unsure |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 17 | 16 | 94.1% | 2 | 0 |
| B | 10 | 9 | 90.0% | 0 | 0 |
| C | 19 | 2 | 10.5% | 1 | 0 |
| D | 3 | 3 | 100.0% | 0 | 0 |

fix は名前空間・出典・引用の訂正も含む。主張の範囲の変更を見るときは status 訂正列を参照。unsure の status は暫定値。

## 主な訂正

- 5.2.2.15 に cartesian fibration での反変輸送と prism を追加。原文の任意の inner fibration に対する述語は範囲外。
- 5.3.1.1 に任意の E→N(C) の strict transport 図式を採用。
- 5.3.1.10 に定義域の cocartesian 辺を保つ関手が張る全部分複体を採用。
- 5.5.2.6 のファイバー同値は原文の hKan 豊穣輸送関手全体の準逆の一部。

## 確認範囲と証拠

- [ch5-evidence.json](ch5-evidence.json) に本文の項目タグと節ページの SHA-256、段1・段1′の記載 ID、探索語、番号のヒット、候補の宣言名と位置を記録した。
- [ch5-kernel-evidence.json](ch5-kernel-evidence.json) に段1・段1′の集計から採用できなかった追加候補の Lean 出力と、既存集計から再利用した ID を記録した。既にビルド済みのモジュールを読み込み、指定の --wait 1800 のロックを使用した。
- check=not_found は対応宣言を採用しなかった行。元の欄が空の場合は、候補探索の結果を表す。check=renamed は名前補正と新たな引用の検査を含む。
- 「なし」は SerrePositivity と固定版 Mathlib の宣言見出し・周辺コメント・番号を探索した範囲の判定。語による順位付けは同義語のすべてを網羅するものではない。
- 所定の 7 列、元表と同一の番号・順序、重複なし、採用した引用と検査結果の対応を確認。標準3公理以外を含む採用行は 0 件。

## やり直し（11-07）

§7 の対象として、前回の own・both・mathlib 62 件と、none 181 件、unsure 0 件を再照合した。
採用した宣言の型は [kernel の記録](ch5-kernel-evidence.json) の `depth_review`、none の番号・タグ、対語を含む型検索、同小節の近接宣言は [行ごとの検索記録](ch5-none-search.json) に置いた。
引用は原典の `citations.csv` 9,711 件と、基点のソースのコメント・タグの再走査で照合した。小節内に own・both の採用先がない行は、近傍を選ぶ代替の起点を検索記録に明記した。

| status | 件数 |
| --- | ---: |
| own | 41 |
| both | 0 |
| mathlib | 6 |
| partial | 125 |
| none | 173 |

ok 183 件、fix 162 件、unsure 0 件。

- 5.1.4.11 は partial。仮定：S は Kan 複体、q:X→S（Lean が強い：引用する向きは q が cocartesian fibration と仮定）。結論：q は単射な前合成同値を右に持ち上げ、内ファイブレーションと可逆辺持ち上げの組としての isofibration となる（Lean が弱い：Kan 底での三条件すべての同値は確認していない）。
- 5.1.7.10 は partial。仮定：同じ底上の二つの内ファイブレーションと比較 F、両全空間は ∞ 圏（Kerodon と一致）。結論：ファイバーの同値から F の本質的全射性が従い、F が充満忠実なら全空間の ∞ 圏同値になる（Lean が弱い：任意の内ファイブレーションで底上の逆とファイバーの同値を両方向に比較する型は未確認）。
- 5.3.1.8 は partial。仮定：通常圏の nerve 上の cocartesian fibration（Kerodon と一致）。結論：各 c で恒等射評価が strict transport の値から元のファイバーへの ∞ 圏同値（Lean が弱い：これらを hQCat での自然同型にする作用の整合性は型にない）。
- 5.5.4.1 は own。仮定：小さな ∞ 圏を QuasicategoryObject として束ねる。SimplicialNerve は任意の単体豊穣圏を取れる（Kerodon と一致）。結論：quasicategoryObject_enrichedCategory は Hom に内部 Hom Fun(C,D) を取り、SimplicialNerve をこの豊穣圏に適用すると太字 QC の単体集合を得る（一致）。
- 5.5.5.1 は own。仮定：小さな ∞ 圏の圏 CatInfinity と、その頂点としての Δ⁰（Kerodon と一致）。結論：sliceUnder は指定した図式を固定する join の延長を束ねる。Δ⁰ を表す pointKanObject の基礎単体集合を CatInfinity の頂点に取り、原文の QC の coslice を得る（一致）。
- 5.5.5.2 は own。仮定：Quasicategory X と図式 p:K→X（Lean が弱い：CatInfinity の一点に限らず任意の図式）。結論：sliceUnder_quasicategory は coslice の ∞ 圏性、sliceUnderProjection_leftFibration は X への射影の左ファイブレーション性（一致）。
- 5.6.6.20 は partial。仮定：F は同じ底上の left fibration 間の射、始域の頂点 x は始対象（Lean が強い：引用補題は F の同値を仮定）。結論：同値 F は x を始対象に写す（Lean が弱い：F(x) の始対象性から F の同値性を得る方向は未確認）。
- 5.6.7.8 は partial。仮定：共通の底上の cocartesian fibration の比較 F（Lean が強い：相対逆の補題は ∞ 圏の底上の left fibration に限定）。結論：全空間での圏同値を前合成同値に読み替え、left fibration の場合に底上の逆と相対単位・余単位を取る（Lean が弱い：任意の cocartesian fibration の相対逆は未確認）。

前回からの status の変更は none → own が 3 件、none → partial が 5 件、own → partial が 18 件。

## 交差検査後の再確認（11-07）

[抜き取り結果](cross-5.md) の seed は `0xf261f37c`。none の誤りは 3/20 件だったため、`9b689a718` を取り込んでから none の 173 行を再確認した。

[行ごとの検索記録](ch5-none-search.json) の `cross_recheck` に、同じ小節と前後の小節の引用先の型、特例・片方向・双対を別々に調べた語、Mathlib の概念名、候補の型見出しと判定理由を記録した。型は参照 ID で引ける。採用した型と公理は [kernel の記録](ch5-kernel-evidence.json) の同名の節にある。

| 判定 | 再確認した行の件数 | 章全体の件数 |
| --- | ---: | ---: |
| own | 1 | 42 |
| both | 0 | 0 |
| mathlib | 0 | 6 |
| partial | 54 | 179 |
| none | 118 | 118 |

ok 130 件、fix 215 件、unsure 0 件。今回採用した宣言が依存する公理は標準三公理の範囲内。

- 5.3.4.19 は own。重み付き nerve の cocartesian strict transport への自然変換があり、各成分は圏同値。
- 5.3.6.9 は partial。関手圏の射影の cartesian fibration 性と、cocartesian 辺の可逆化から cartesian 辺を得る方向を確認した。
