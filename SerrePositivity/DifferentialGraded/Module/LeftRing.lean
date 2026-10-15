module
public import SerrePositivity.DifferentialGraded.Module.LeftAction
public import SerrePositivity.DifferentialGraded.Module.Ring

/-! # 一対象環A上の左dg加群 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 任意非有界複体を一対象環A上の左加群とする。 -/
abbrev ringLeftModule (P : Complex A) : LeftModule A PUnit.{1} where
  obj _ := P
  map _ _ := identity P
  map_id _ := by
    change 𝟙 _ ≫ identity P = identity P
    exact Category.id_comp _
  map_comp _ _ _ := by
    change (λ_ (𝟙_ (Complex A))).hom ≫ identity P =
      (identity P ⊗ₘ identity P) ≫ enrichedComposition P P P
    exact (identity_tensor_comp A (identity P)).symm

/-- 一対象環上の左作用も単位保存から一意に定まる。 -/
lemma ringLeftModule_map (N : LeftModule A PUnit.{1}) (x : PUnit.{1}) :
    N.map x x = identity (N.obj x) := by
  have h := N.map_id x
  change 𝟙 _ ≫ N.map x x = identity (N.obj x) at h
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded
