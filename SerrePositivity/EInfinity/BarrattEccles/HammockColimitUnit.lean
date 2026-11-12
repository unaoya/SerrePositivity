module

public import SerrePositivity.EInfinity.BarrattEccles.HammockColimitComposition
public import SerrePositivity.EInfinity.BarrattEccles.HammockUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionUnit

/-!
# 元の E 代数の hammock 合成の左右単位則

概要：任意の可換環上で、同じ元の単位と余極限上の合成の左右単位則を証明する。
方針：実際の弱同値を用いる構成済みの左右単位則へ代入する。
規約：モデル構造を局所的に選び、対象の cofibrancy や追加の instance は要求しない。
使われ方：CAlg_R の高次比較に用いる hammock の豊穣圏の構成。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra MonoidalCategory

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の単位と実際の二つの余極限の積からの合成の左単位則。 -/
lemma algebraHammockColimitComposition_left_unit (X Y : (operad A).Algebra) :
    (algebraHammockColimitUnit A X ⊗ₘ 𝟙 (algebraHammockColimitGraph A X Y)) ≫
        algebraHammockColimitComposition A X X Y =
      (λ_ (algebraHammockColimitGraph A X Y)).hom := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_left_unit (weakEquivalences (operad A).Algebra) X Y

/-- 元の単位と実際の二つの余極限の積からの合成の右単位則。 -/
lemma algebraHammockColimitComposition_right_unit (X Y : (operad A).Algebra) :
    (𝟙 (algebraHammockColimitGraph A X Y) ⊗ₘ algebraHammockColimitUnit A Y) ≫
        algebraHammockColimitComposition A X Y Y =
      (ρ_ (algebraHammockColimitGraph A X Y)).hom := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_right_unit (weakEquivalences (operad A).Algebra) X Y

/-- 全固定語の元の標準射上で、左単位則は同じ単位同型を回収する。 -/
lemma algebraHammockColimitComposition_left_unit_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (X Y : (operad A).Algebra) :
    (algebraHammockColimitUnit A X ⊗ₘ algebraHammockGraphInclusion A a X Y) ≫
        algebraHammockColimitComposition A X X Y =
      (λ_ (algebraHammockGraph A a X Y)).hom ≫ algebraHammockGraphInclusion A a X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_left_unit_fac (weakEquivalences (operad A).Algebra) X Y a

/-- 全固定語の元の標準射上で、右単位則も同じ単位同型を回収する。 -/
lemma algebraHammockColimitComposition_right_unit_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (X Y : (operad A).Algebra) :
    (algebraHammockGraphInclusion A a X Y ⊗ₘ algebraHammockColimitUnit A Y) ≫
        algebraHammockColimitComposition A X Y Y =
      (ρ_ (algebraHammockGraph A a X Y)).hom ≫ algebraHammockGraphInclusion A a X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_right_unit_fac (weakEquivalences (operad A).Algebra) X Y a

end SerrePositivity.EInfinity.BarrattEccles
