module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitDerivedHomNormalization
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitAdjunction

/-!
# 局所化随伴と元の通常錐からの射の一致

概要：BM 命題 4.1・Hovey §5.4 の局所化随伴を通常錐の比較で正規化する。
方針：同じ導来 Hom 同値の計算を局所化圏全体の随伴へ戻す。
規約：元の錐の射と計算対象への比較を保持する。
使われ方：元の極限比較を持つ右導来関手の普遍性。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：局所化随伴の Hom 対応は元の通常錐の比較を回収（Hovey §5.4）。
方針：元の対象の像での Hom 対応に通常錐の正規化を代入する。
規約：元の比較同型と元の coneToFramedLimit を使う。
使われ方：通常の極限比較の右導来性の証明。 -/
lemma framedLimitAdjunction_homEquiv_cone (F : K ⥤ (operad A).Algebra) (c : Cone F) :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    (framedLimitAdjunction A K).homEquiv (Q.obj c.pt) (QD.obj F)
        ((localizedConstantDiagramComparison A K).hom.app c.pt ≫ QD.map c.π) ≫
      (localizedFramedLimitComparison A K).hom.app F = Q.map (coneToFramedLimit A K F c) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  exact (framedLimitAdjunction_homEquiv_comparison A K c.pt F _).trans
    (framedLimitDerivedHomEquiv_cone A K F c)

end SerrePositivity.EInfinity.BarrattEccles
