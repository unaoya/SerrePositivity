module
public import SerrePositivity.DifferentialGraded.Tensor.HomComposition

/-! # balanced tensorの各変数に関するdg関手 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群を固定したbalanced tensorのdg関手。 -/
def rightTensorDG (N : LeftModule A D) : DGFunctor A (RightModule A D) (Complex A) :=
  DGFunctor.ofHomMaps A (fun M => obj A D M N) (fun M M' => rightHomMap A D M M' N)
    (fun M => rightHomMap_unit A D M N)
    (fun _ _ _ _ _ _ hk τ σ => rightHomMap_forward A D N τ σ hk)

/-- 右加群を固定したbalanced tensorのdg関手。 -/
def leftTensorDG (M : RightModule A D) : DGFunctor A (LeftModule A D) (Complex A) :=
  DGFunctor.ofHomMaps A (fun N => obj A D M N) (fun N N' => leftHomMap A D M N N')
    (fun N => leftHomMap_unit A D M N)
    (fun _ _ _ _ _ _ hk τ σ => leftHomMap_forward A D M τ σ hk)

end SerrePositivity.DifferentialGraded.BalancedTensor
