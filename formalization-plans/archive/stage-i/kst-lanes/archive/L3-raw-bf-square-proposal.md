# K-B：有限 native BF 四角形比較の旧四対象固定型（条件付きで保持）

概要：同じ D-9 の未完備実列の一四角形を、同じ cone の構造辺へ渡す有限比較。
方針：同じ四 BF 頂点の間で新 coherent BF 四辺を同時構成し、旧 BF 射とは正段の指定比較と全整数 π 作用の一致を保持する。
規約：ユーザー採用の型変更。旧 kSpectrumMap の辺との厳密等式・全 Sp 写像空間内比較は要求しない。固定 S・ν・K、I・P、既存の条件付き屋根は保持する。
使われ方：元の全 S• 四角形の比較から、新 coherent 右辺の実 fiber・同じ cone の構造辺へ接続する。

## 供給範囲

- 一般 BF 高次面整流や一般 StableInfinity 上の K 関手化は再開しない。同じ D-9 の厳密 dg 実列の一つの native 提示だけに限る。
- `DGKappaNativeBFBoundaryInput` は既存 hBF のデータ表示であり、独立した存在仮定の追加ではない。四つの実 BF 対象は保持し、新四辺をそれらの間の BF 射として受け取る。
- `bottom`・`right`・`left`・`top` はこの四角形のための新 coherent BF 射。Φ の境界はこれらの新射の coherent 辺として厳密に回収する。
- 各 `_positive` は全 r で新旧の実辺の正段空間値図式の指定比較。各 `_pi` は全整数 j で `OmegaSpectrum.homotopyMap` が旧 kSpectrumMap と一致すること。辺・hSp 射の等式に強めない。
- `positive` は各正段の Φ 全体を同じ元の S• 境界商の全四角形へ比較する。個別の四辺比較や π 群だけでは代用しない。
- K-S•-S3 は `dgKappaNativeCoherentBFSquare`・`dgKappaNativeCoherentBFArrow`・`dgKappaNativeCoherentBFPositiveComparison`・`dgKappaNativeCoherentBFArrow_homotopyMap_eq` を実供給済み。ただし BF 四対象自体が新しい有限 BF 模型で、整数群の式は指定群同型との可換式。以下の旧四対象固定命題の証明としては扱わない。実供給は DGKappaSuppliedBF* の利用側へ直接消費し、固定 K への二頂点比較は archive/L3-supplied-bf-vertex-comparison.md の設計補足で扱う。

## 条件付きで保持する旧四対象固定命題

全フィールドの型の正本は `SerrePositivity/KST/NonConnective/DGKappaNativeBFBoundaryInput.lean`。以下は `/tmp/kb-s3-current-request.lean` で型検査済み。

```lean
import SerrePositivity.KST.NonConnective.DGKappaNativeBFBoundaryInput
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
universe u v
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
def kbRawBFSquareRequest : Prop := Nonempty (DGKappaNativeBFBoundaryInput R D I)
```

## 利用側

- `DGKappaNativeBFSquare` は同じ新四辺から元の四頂点を回収し、元の正段全四角形比較と S• 引き戻しの消費を保持する。
- `DGKappaNativeBFArrowComparison` は同じ四辺だけを添字付け、指定正段比較・全整数 π 一致を回収する。旧 K-cof による正次数全単射・零次単射はこの π 一致で移す。対応する元の完全射の完備化性が適用条件であり、実商射の完備化性は主張しない。
- `DGKappaNativeBFRightArrow` は実 Φ から読み戻す右辺を同じ新 BF 射へ厳密回収し、その π 作用を旧 BF 商射へ比較する。実 fiber はこの新右辺を底とする。旧射と新射の π 作用が一致することだけから、旧射の Sp fiber との同型は推論しない。
- 同じ実商の Yoneda 完備化に対する既存 hcofinal と、固定 K へ戻す P・loop 比較は保持する。新たな完備化存在や全入力自然性は要求しない。
