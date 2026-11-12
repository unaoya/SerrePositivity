module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Objects
public import Mathlib.Logic.Small.Basic

/-! 小さい二つの dg 圏の gluing の対象も、同じ係数宇宙で小さい。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- gluing の対象は、元の両対象と同じ係数複体の閉元の従属和。 -/
def dgGluingObjectEquiv :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M ≃ Σ c : C, Σ d : D, zeroCycles (M.value c d) where
  toFun X := ⟨X.left, X.right, X.gluing⟩
  invFun X := ⟨X.1, X.2.1, X.2.2⟩
  left_inv X := by cases X; rfl
  right_inv X := by rcases X with ⟨c, d, h⟩; rfl

/-- 両圏が係数宇宙で小さければ、gluing の右加群も同じ宇宙で構成できる。 -/
instance dgGluingSmall : Small.{u} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  small_of_injective (dgGluingObjectEquiv R C D M).injective

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
