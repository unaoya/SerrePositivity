module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxValues

/-! # max の一左端点の元の生成元での値
概要：一左端点による定数作用を、元の二端点と辺で正規化する。
方針：元の増大写像の生成元での値を回収する。
規約：単位の元と元の生成元を保持する。使われ方：三重作用と max の結合則の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 一端点と零端点の max は元の一端点。 -/
lemma serreIntervalMax_one_zero :
    (serreIntervalMax A).f 0 (ιTensorObj (serreInterval A) (serreInterval A) 0 0 0 rfl
      ((cycleFromUnit _ (serreIntervalOne A)).val ⊗ₜ[A]
        (cycleFromUnit _ (serreIntervalZero A)).val)) =
      (cycleFromUnit _ (serreIntervalOne A)).val := by
  rw [serreIntervalMax_one_apply, chain_comp_apply, serreIntervalAugmentation_zero_value]
  rfl

/-- 二つの一端点の max は元の一端点。 -/
lemma serreIntervalMax_one_one :
    (serreIntervalMax A).f 0 (ιTensorObj (serreInterval A) (serreInterval A) 0 0 0 rfl
      ((cycleFromUnit _ (serreIntervalOne A)).val ⊗ₜ[A]
        (cycleFromUnit _ (serreIntervalOne A)).val)) =
      (cycleFromUnit _ (serreIntervalOne A)).val := by
  rw [serreIntervalMax_one_apply, chain_comp_apply, serreIntervalAugmentation_one_value]
  rfl

/-- 一端点と元の辺の max は零。 -/
lemma serreIntervalMax_one_edge :
    (serreIntervalMax A).f (-1)
      (ιTensorObj (serreInterval A) (serreInterval A) 0 (-1) (-1) (by omega)
        ((cycleFromUnit _ (serreIntervalOne A)).val ⊗ₜ[A] serreIntervalEdge A)) = 0 := by
  rw [serreIntervalMax_one_apply, chain_comp_apply, serreIntervalAugmentation_edge, map_zero]

end SerrePositivity.KST.SConstruction
