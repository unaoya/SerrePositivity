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
