# Ch 1 対応表確認結果（2026-11-07 JST）

対象はitems.csvのCh 1全180項目。結果は[chapter CSV](../ch1.csv)。新しい数学の宣言は追加していない。
原文の取得先と保存時のhashはch1-source-index.json、個別の照合判断はch1-semantic-decisions.json。

判定：ok 121、fix 54、unsure 5。check：found 95、renamed 56、not_found 29。

宣言あり151項目は、最終CSVで引用した名前について#checkと#print axiomsの成功出力を確認した。
ch1-kernel-evidence.jsonは各引用と生出力を結び付ける。追加公理は検出されなかった。
これは引用した宣言についての結果であり、段1全3,553項目の完了報告ではない。

noneの29項目のcheck=not_foundは「対応宣言をソース探索で見つけなかった」の意味である。
未指定の宣言に対する#checkが失敗したという意味ではない。検索式・範囲・生結果はch1-none-search.json。
探索範囲はSerrePositivity全体とMathlibのAlgebraicTopology/CategoryTheory、および近傍の宣言・docstring。
検索ヒットの類似名・別対象・逆向きの命題を、原文に対応する宣言と混同しないよう照合した。

## 主な訂正

- CategoryTheory、SerrePositivity.SimplicialModel、InfinityCategories.Kanなどの名前空間を補正。
- 匿名インスタンスの説明を環境から取得した実名に変更。記法やEquiv.symmの射影は元の名前付き構成を引用。
- 1.1.3.9：原文の単体圏はX.Elementsの反対圏。SSet.Sは前順序であり異なる。
- 1.2.5.10：KanHomotopyZero.equivPiZeroによるπ₀比較を追加。
- 1.4.6.12：Kan複体のhXの亜群性と、一般のhXにFreeGroupoidを適用する定義を区別。
- 1.5.7.1：IsPrecompositionEquivalenceをtrivial Kan fibrationそのものとは扱わず、可算spineのinner anodyne性と一般の制限補題で特例を明示。

## 未確定の主張

- 1.1.2.10：原文は5条件。退化作用素の像・低次元への全射・低次元への任意射の対応は確認。任意次元への非単射写像による因子化まで含む全5条件の同値は未確認。
- 1.1.4.13：Mathlibのhom_extは単射性、自前のboundaryFaceGluingは次元n+2の全射性。原文が含む1次元の貼合せまで引用先だけで網羅するか未確認。引用の名前空間も補正が必要。
- 1.4.5.7：原文は指定uによるHom全単射。引用された比較同値と自然性の型を確認したが、原文のuとの整合まで未確認。正しい名前空間はHomotopyCategoryMap。
- 1.5.5.5：切断の存在は一致。引用するホモトピーの型はid→s∘pで、原文の指定するs∘p→idとは端点順序が逆。そのまま同じ主張とは判定しない。
- 1.5.5.11：引用先の型は終域のKan性・可縮性から始域への遷移で、原文の始域から終域への三つの遷移と逆。対応する方向の別宣言は未確認。KanMonoArrowFactorization側の名前空間も補正が必要。

これらは未確認をokに変えずunsureで残した。原文に対する主張のずれの判断と、宣言の実在・公理の検査は別である。

## 検証

180行、番号と順序が元表に一致、重複なし、所定7列、checkの未解決なしを確認。
宣言なし29項目のcheck以外は、全て生出力のfoundに結び付く。
最終の引用で標準3公理以外は0件。ModelCategoryという型仮定も最終引用の型からは検出されなかった。
段1全件runは裏で継続する。mainへの取り込みは調整役が行う。
