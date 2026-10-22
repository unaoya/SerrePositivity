module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Category
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComparisonProjections

/-! 元の二つの Hom 射影を用いる dg 射影と、左射影の Yoneda 比較。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
lemma dgGluingLeftModule_map (X Y : DGGluingObject R C D M) :
    (dgGluingLeftModule R C D M).map X Y =
      dgGluingLeftHomMap R C D M X Y ≫ yonedaHom R C X.left Y.left :=
  dgGluingHomRepresentableIso_left R C D M X Y
lemma dgGluingLeftHomMap_id (X : DGGluingObject R C D M) :
    eId (Complex R) X ≫ dgGluingLeftHomMap R C D M X X = eId (Complex R) X.left := by
  have : IsIso (yonedaHom R C X.left X.left) := by
    change IsIso (dgYonedaIso R X.left (representable R X.left)).inv
    infer_instance
  apply (cancel_mono (yonedaHom R C X.left X.left)).1
  have h := (dgGluingLeftModule R C D M).map_id X
  rw [dgGluingLeftModule_map] at h
  have hY := (dgYoneda R C).map_id X.left
  change eId (Complex R) X.left ≫ yonedaHom R C X.left X.left =
    eId (Complex R) (representable R X.left) at hY
  rw [Category.assoc, hY]
  exact h
lemma dgGluingLeftHomMap_comp (X Y Z : DGGluingObject R C D M) :
    eComp (Complex R) X Y Z ≫ dgGluingLeftHomMap R C D M X Z =
      (dgGluingLeftHomMap R C D M X Y ⊗ₘ dgGluingLeftHomMap R C D M Y Z) ≫
        eComp (Complex R) X.left Y.left Z.left := by
  have : IsIso (yonedaHom R C X.left Z.left) := by
    change IsIso (dgYonedaIso R X.left (representable R Z.left)).inv
    infer_instance
  apply (cancel_mono (yonedaHom R C X.left Z.left)).1
  have h := (dgGluingLeftModule R C D M).map_comp X Y Z
  simp only [dgGluingLeftModule_map] at h
  have hY := (dgYoneda R C).map_comp X.left Y.left Z.left
  change eComp (Complex R) X.left Y.left Z.left ≫ yonedaHom R C X.left Z.left =
    (yonedaHom R C X.left Y.left ⊗ₘ yonedaHom R C Y.left Z.left) ≫
      eComp (Complex R) (representable R X.left) (representable R Y.left)
        (representable R Z.left) at hY
  simp only [Category.assoc]
  rw [hY]
  simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc] using! h

def dgGluingLeft : DGFunctor R (DGGluingObject R C D M) C where
  obj := DGGluingObject.left
  map := dgGluingLeftHomMap R C D M
  map_id := dgGluingLeftHomMap_id R C D M
  map_comp := dgGluingLeftHomMap_comp R C D M
lemma dgGluingRight_map (X Y : DGGluingObject R C D M) :
    (dgGluingRight R C D M).map X Y = dgGluingRightHomMap R C D M X Y :=
  dgGluingHomRepresentableIso_right R C D M X Y
lemma dgGluingLeft_comp_yoneda :
    (dgGluingLeft R C D M).comp (dgYoneda R C) = dgGluingLeftModule R C D M := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgGluingLeft R C D M).comp (dgYoneda R C))
    (G := dgGluingLeftModule R C D M) (fun _ ↦ rfl)
  intro X Y
  simpa only [EnrichedFunctor.comp_map, dgGluingLeft, eqToHom_refl,
    Category.comp_id] using! (dgGluingLeftModule_map R C D M X Y).symm

end SerrePositivity.InfinityCategories
