module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullLimitReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback

/-! # 充満 dg 部分圏による引き戻し四角形の反映

概要：部分圏内の四角形が周囲の dg nerve で引き戻しなら、部分圏でも引き戻しである。
方針：対応する錐の包含像を比較し、極限性の反映を使う。
規約：HTT §1.2.13。使われ方：閉性から構成した標準 fiber 四角形の極限性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : D → Prop)

/-- 概要：部分圏の四角形の包含像が引き戻しなら、元の四角形も引き戻し。
方針：正方形から作る錐と包含による後合成が可換であることを定義から読み、極限性の反映を使う。
規約：HTT §1.2.13。使われ方：標準 fiber の四角形を充満 dg 部分圏に制限する。 -/
lemma isPullbackSquare_of_fullInclusion
    (F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isLimitCone_of_fullInclusion A D P (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)
  exact hF

/-- 概要：全対象が P を持つ一単体の Yoneda 射を持ち上げると包含で元に戻る。
方針：Yoneda の後合成の式と liftToFull の包含像の公式を使う。
規約：HA Construction 1.3.1.6。使われ方：標準三角形を部分圏へ持ち上げて貼り合わせる。 -/
lemma liftToFull_yoneda_inclusion {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) (hs : ∀ i, P (s.obj i)) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull A D P s hs) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P) = SSet.yonedaEquiv.symm s := by
  rw [SSet.yonedaEquiv_symm_comp]
  congr 1

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
