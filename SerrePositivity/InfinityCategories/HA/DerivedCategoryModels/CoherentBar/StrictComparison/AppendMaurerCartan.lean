module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.EndDifferential

/-!
概要：実正規化 bar 上の末尾付加作用素の微分を、二つの theta 合成へ帰着する。
方針：内部微分の消滅と次数 −1 の MC 自己 Hom 微分公式を使う。
規約：縮約恒等式の右辺との一致は後続の列計算で示す。
使われ方：有限 support 上の局所縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

local notation "B" => ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F))
local notation "P" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictNormalizedModule R D F
local notation "T" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)

lemma dgStrictAppendHom_d (b : J) :
    (moduleHom R D P P).d (-1) 0 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendHom R D F b) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndRebase R D F 0
        (compose R (x := B) (y := B) (z := B) T (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendGradedHom R D F b)
          (show (-1 : ℤ) + 1 = 0 by omega) +
        compose R (x := B) (y := B) (z := B) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendGradedHom R D F b) T
          (show (1 : ℤ) + -1 = 0 by omega)) := by
  have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndDifferential R D F (-1) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendGradedHom R D F b) =
      compose R (x := B) (y := B) (z := B) T (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendGradedHom R D F b)
        (show (-1 : ℤ) + 1 = 0 by omega) +
      compose R (x := B) (y := B) (z := B) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendGradedHom R D F b) T
        (show (1 : ℤ) + -1 = 0 by omega) := by
    unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndDifferential
    erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendGradedHom_d R D F b]
    simp only [neg_add_cancel, Int.negOnePow_zero, one_smul, zero_add]
  have hd := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndRebase_d R D F (-1) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendGradedHom R D F b)
  exact hd.trans (congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndRebase R D F 0) he)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
