module
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-! # 小さい二つのdg圏のtensor積の対象のsmall性 -/
@[expose] public section
universe u v w
namespace SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

instance dgTensorSmall : Small.{u} (DGTensorCategory A B C) :=
  inferInstanceAs (Small.{u} (B × C))

end SerrePositivity.DifferentialGraded
