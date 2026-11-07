# Ch 6 対応表確認結果（2026-11-07 JST）

対象は items.csv の Ch 6 全 145 項目。結果は [章 CSV](../ch6.csv)。確認用の Lean コマンドは既存宣言の型・公理・instance を調べるものに限った。

判定は ok 67 件、fix 78 件、unsure 0 件。check は found 11 件、renamed 76 件、not_found 58 件。

## 判定の内訳

| 元の status | ok | fix | unsure |
| --- | ---: | ---: | ---: |
| own | 0 | 19 | 0 |
| mathlib | 5 | 12 | 0 |
| both | 0 | 5 | 0 |
| partial | 6 | 39 | 0 |
| none | 56 | 3 | 0 |

| 優先理由 | 対象 | fix | fix の率 | status 訂正 | unsure |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 9 | 9 | 100.0% | 1 | 0 |
| B | 0 | 0 | — | 0 | 0 |
| C | 8 | 0 | 0.0% | 0 | 0 |
| D | 2 | 2 | 100.0% | 1 | 0 |

fix は名前空間・出典・引用の訂正も含む。主張の範囲の変更を見るときは status 訂正列を参照。unsure の status は暫定値。

## 主な訂正

- 6.1.2.8 の右 zigzag の冪等性は Mathlib にある。片側逆を仮定した帰結は冪等式の消去。
- 6.2.1.14 の原文はホモトピー圏に降ろした単位だけを調べる。引用の全試験 ∞ 圏による判定との範囲の違いを明記。
- 6.2.5.4・6.2.5.7 は Quillen 随伴の cf collage に限った partial。両圏にモデル圏構造を仮定する。
- 6.3.6.17 は有限 poset からの普遍的局所化の存在。Mathlib の poset の nerve の非特異性に付く 02MT は、現行本文の Remark 6.3.6.16 のタグ。6.3.6.17 のタグは 02MU。

## 確認範囲と証拠

- [ch6-evidence.json](ch6-evidence.json) に本文の項目タグと節ページの SHA-256、段1・段1′の記載 ID、探索語、番号のヒット、候補の宣言名と位置を記録した。
- [ch6-kernel-evidence.json](ch6-kernel-evidence.json) に段1・段1′の集計から採用できなかった追加候補の Lean 出力と、既存集計から再利用した ID を記録した。既にビルド済みのモジュールを読み込み、指定の --wait 1800 のロックを使用した。
- check=not_found は対応宣言を採用しなかった行。元の欄が空の場合は、候補探索の結果を表す。check=renamed は名前補正と新たな引用の検査を含む。
- 「なし」は SerrePositivity と固定版 Mathlib の宣言見出し・周辺コメント・番号を探索した範囲の判定。語による順位付けは同義語のすべてを網羅するものではない。
- 所定の 7 列、元表と同一の番号・順序、重複なし、採用した引用と検査結果の対応を確認。標準3公理以外を含む採用行は 0 件。
- 6.2.5.4・6.2.5.7 の原文は任意のファイバーを扱う。引用は任意の圏 C・D に [ModelCategory C]・[ModelCategory D] と単体豊穣を要求し、具体的な SSet での #synth ModelCategory SSet も失敗した。ModelBridge/Inputs/KanQuillen.lean の kanQuillenModel は文献入力を使う def。

## やり直し（11-07）

§7 の対象として、前回の own・both・mathlib 41 件と、none 58 件、unsure 0 件を再照合した。
採用した宣言の型は [kernel の記録](ch6-kernel-evidence.json) の `depth_review`、none の番号・タグ、対語を含む型検索、同小節の近接宣言は [行ごとの検索記録](ch6-none-search.json) に置いた。
引用は原典の `citations.csv` 9,711 件と、基点のソースのコメント・タグの再走査で照合した。小節内に own・both の採用先がない行は、近傍を選ぶ代替の起点を検索記録に明記した。

| status | 件数 |
| --- | ---: |
| own | 15 |
| both | 0 |
| mathlib | 16 |
| partial | 60 |
| none | 54 |

ok 63 件、fix 82 件、unsure 0 件。

- 6.1.6.13 は partial。仮定：モノイダル圏の X,Y と評価 ev:X⊗Y→𝟙（Lean が強い：ev を ExactPairing Y X の評価と仮定）。結論：tensorRightHomEquiv Z Y X 𝟙 の逆は、左単位子で 𝟙⊗X を X と同一視して、指定評価による Hom(Z,X)→Hom(Z⊗Y,𝟙) の全単射を与える（Lean が弱い：任意の ev の弱双対を定める述語は未確認）。
- 6.2.3.16 は partial。仮定：∞ 圏 X と辺集合 W。各 x に W-局所同値で W-局所対象へ向かう辺を仮定（原文の局所置換に対応）（Kerodon と一致）。結論：W-局所対象の全部分圏の反射性と随伴を確認。反射が反転する集合に関する局所化もある（Lean が弱い：localizing の全条件から、反転される集合が元の W と一致する判定は未確認）。
- 6.3.2.12 は partial。仮定：単体集合のフィルター図式（Lean が強い：単射の可算列で初頂点射だけを扱う）。結論：各段の初頂点射が初頂点を保つ辺に関して局所化なら、余極限でも同種の局所化（Lean が弱い：任意の arrow 図式と指定辺の像の和集合には及ばない）。
- 6.3.5.9 は partial。仮定：射 L と逆向きの I、各変形成分の辺を反転させる仮定（Lean が強い：Fun の相対的な同じ成分という条件の代わりに明示的な単体ホモトピーを用いる）。結論：L が指定辺に関する局所化（Lean が弱い：任意の底変換での局所化を結論しない）。
- 6.2.5.4 と 6.2.5.7 は partial。Quillen 随伴の cf collage は両圏に ModelCategory を仮定する。SSet の instance が合成できない結果は kernel の記録に残した。

前回からの status の変更は both → partial が 3 件、mathlib → partial が 4 件、none → partial が 4 件、own → partial が 3 件。
