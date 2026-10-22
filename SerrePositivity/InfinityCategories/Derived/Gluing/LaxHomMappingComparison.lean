module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomMappingModel
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedLaxComparison

/-! 同じ mapping cocone 複体模型から、実導来 lax pullback の写像空間への比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
local notation "F" => dgGluingUniverseDerivedNerveLaxComparison R C D M

def dgGluingLaxHomMappingComparison (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
    InfinityCategories.pinchedHom
      (X := F2.laxPullback (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
      ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
      ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y))) :=
  (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
    pinchedHomMap (F) (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y))

lemma dgGluingLaxHomMappingComparison_source (X Y : DGGluingObject R C D M) :
    (dgGluingUniverseHomMappingIso R C D M X Y).hom ≫
      dgGluingLaxHomMappingComparison R C D M X Y =
    pinchedHomMap (F) (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) := by
  rw [dgGluingLaxHomMappingComparison, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end SerrePositivity.InfinityCategories
