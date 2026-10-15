module
public import SerrePositivity.DifferentialGraded.Tensor.SwapNaturality
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionLaws

/-! # balanced tensorの左加群変数における余極限保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 固定右加群とのbalanced tensorを閉零左加群圏上の関手にする。 -/
def leftTensorFunctor (M : RightModule A D) : LeftModuleCategory A D ⥤ Complex A where
  obj N := obj A D M (ForgetEnrichment.to (Complex A) N)
  map g := map A D (𝟙 (ForgetEnrichment.of (Complex A) M)) g
  map_id N := map_id A D (ForgetEnrichment.of (Complex A) M) N
  map_comp f g := by
    simpa only [Category.id_comp] using
      map_comp A D (𝟙 (ForgetEnrichment.of (Complex A) M))
        (𝟙 (ForgetEnrichment.of (Complex A) M)) f g

/-- 左加群変数のtensorは、oppositeでの右加群変数のtensorと自然同型。 -/
def leftTensorSwapIso (M : RightModule A D) :
    leftTensorFunctor A D M ≅
      leftModuleToRightOpposite A D ⋙ rightTensorFunctor A Dᵒᵖ M.toFunctor :=
  NatIso.ofComponents (fun N => swapIso A D M (ForgetEnrichment.to (Complex A) N))
    (fun g => swapHom_naturality_left A D M g)

/-- 存在する任意サイズの余極限を左加群変数でも保存する。 -/
instance leftTensorFunctor_preservesColimits (M : RightModule A D) :
    PreservesColimitsOfSize.{w, t} (leftTensorFunctor A D M) :=
  preservesColimits_of_natIso (leftTensorSwapIso A D M).symm

end SerrePositivity.DifferentialGraded.BalancedTensor
