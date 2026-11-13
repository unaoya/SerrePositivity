# Bhatt–Scholze の配置

対応表と文献の版は [BS coverage](../../research/bs-coverage/) と [bibliography.json](../../research/bibliography.json) を参照する。宣言の文献対応は `@[cite BS19 "番号"]`、部分対応は理由付きで記し、`#cite_tags BS19` で実際の定義元と場所を照会する。

- `Delta/`・`Prism/`：δ環と prism の基礎。分冪の δ 環固有の計算は `Delta/DividedPower/{Coefficients,RegularSequence,Frobenius,Principal,PDivision}/` に分け、相対完全正則性の一般部分は `Delta/CompleteRegularity/` に置く。Construction 6.1 の crystalline cover は `Prismatic/HodgeTate/Comparison/CrystallineCover/` にまとめる。
- `Prismatic/Crystalline/`：Theorem 5.2 の比較、crystalline site と Poincaré の構成。Theorem 6.4 を主題とする PD・Witt 比較は `Prismatic/HodgeTate/Comparison/Witt/` に置く。
- `Prismatic/CechAlexander/`：frame、envelope、複体と Čech–Alexander 比較。
- `Prismatic/HodgeTate/`：Hodge–Tate 比較、係数、Witt、基底変換。
- `Semiperfectoid/Lci/`：Example 7.9 の lci 構成。ほかの semiperfectoid の基礎は親ディレクトリに残す。
- `Perfectoidization/Arc/`：arc site、付値環、Milnor、descent。積分的 perfectoidization の §10 の構成は `IntegralPerfectoidization/` の近似・完備化・存在・有限étaleへ分ける。

節をまたぐファイルは主な構成の下に一度だけ置き、ほかの節による利用は同じ宣言への引用で表す。ディレクトリ分けだけの移動では既存の公開名前空間を保つ。これは引用を数学的な完全対応へ格上げする操作ではない。元の部分対応・保留を引き継ぐ。

環・加群の一般論は `CommutativeAlgebra/{DividedPowers,Polynomial,CompletelyFlat}/`、導来完備化の一般論は `HomologicalAlgebra/DerivedCompletion/`、余単体的代数の一般の部品は `HomologicalAlgebra/Cosimplicial/Algebra/` に置く。prism 固有の特殊化は BS 側からそれらを import する。

5 段の層は `scripts/refactor/layers.json` の設定で検査する。論文の節の前後と依存の層は別の基準であり、共通の計算を使う節をまたぐ依存は理由を記録する。監査は `scripts/audit/bs_power_root_envelope/` に置く。
