module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomMappingModel

/-! 元 pinched Hom の複体模型への移送と正本の逆移送を相殺し、同じ実持ち上げ Hom を回収。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

lemma dgGluingNativeHomModelCancellation :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (pinchedComplexModelIso (A := R) X Y).hom ≫
      (dgGluingUniverseHomMappingIso R C D M X Y).inv =
      (uliftPinchedHomIso.{max u v w, max (u + 1) v w}
        (C := dgNerve R (DGGluingObject R C D M)) (Simplex.vertex X) (Simplex.vertex Y)).hom := by
  change (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (pinchedComplexModelIso (A := R) X Y).hom ≫
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (pinchedComplexModelIso (A := R) X Y).inv ≫ _) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories
