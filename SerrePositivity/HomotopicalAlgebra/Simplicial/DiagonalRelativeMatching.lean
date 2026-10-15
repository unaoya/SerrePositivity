module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalMatching
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-! # Relative matching maps are the actual boundary pullback-Hom maps

The isomorphism compares both pullback targets and the arrows into them.
It uses the proved boundary matching isomorphism and its target naturality.
No model or SM7 assumption is made here.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.Reedy

namespace SerrePositivity.BisimplicialModel
variable {Z Y : SSet.{v}} (p : Z ⟶ Y) (n : ℕ)

abbrev boundaryRestriction (T : SSet.{v}) (n : ℕ) :=
  (MonoidalClosed.internalHom.map (SSet.boundary.{v} n).ι.op).app T
abbrev boundaryTargetMap := (ihom (SSet.boundary.{v} n).toSSet).map p
abbrev reedyTargetMap :=
  (matchingEvaluation simplexOp (Opposite.op (SimplexCategory.mk n))).map (internalHomRight.map p)
abbrev reedyRestriction (T : SSet.{v}) (n : ℕ) :=
  (matchingComparison simplexOp (Opposite.op (SimplexCategory.mk n))).app (internalHomRight.obj T)

lemma matchingBoundaryIso_inv_naturality :
    reedyTargetMap p n ≫ (matchingBoundaryIso Y n).inv =
      (matchingBoundaryIso Z n).inv ≫ boundaryTargetMap p n := by
  have h := matchingBoundaryIso_naturality p n
  calc
    _ = (matchingBoundaryIso Z n).inv ≫
        ((matchingBoundaryIso Z n).hom ≫ reedyTargetMap p n) ≫
          (matchingBoundaryIso Y n).inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (matchingBoundaryIso Z n).inv ≫
        (boundaryTargetMap p n ≫ (matchingBoundaryIso Y n).hom) ≫
          (matchingBoundaryIso Y n).inv := by rw [h]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma matchingBoundaryIso_inv_restriction (T : SSet.{v}) (n : ℕ) :
    reedyRestriction T n ≫ (matchingBoundaryIso T n).inv = boundaryRestriction T n := by
  calc
    _ = (boundaryRestriction T n ≫ (matchingBoundaryIso T n).hom) ≫
        (matchingBoundaryIso T n).inv :=
      congrArg (fun k => k ≫ (matchingBoundaryIso T n).inv) (matchingBoundaryIso_fac T n).symm
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

abbrev boundaryPullbackHom : MonoidalClosed.internalHom.PullbackObjObj (SSet.boundary.{v} n).ι p :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

abbrev relativeTarget := pullback (reedyRestriction Y n) (reedyTargetMap p n)

abbrev targetMap : pullback (reedyTargetMap p n) (reedyRestriction Y n) ⟶
    (boundaryPullbackHom p n).pt :=
  pullback.map _ _ _ _ (matchingBoundaryIso Z n).inv (𝟙 _) (matchingBoundaryIso Y n).inv
    (matchingBoundaryIso_inv_naturality p n)
    ((matchingBoundaryIso_inv_restriction Y n).trans (Category.id_comp _).symm)

instance targetMap_isIso : IsIso (targetMap p n) := by
  exact pullback.map_isIso _ _ _ _ _ _ _ _ _

/-- The actual relative matching pullback is the actual boundary pullback-Hom target. -/
def relativeTargetIso : relativeTarget p n ≅ (boundaryPullbackHom p n).pt :=
  pullbackSymmetry _ _ ≪≫ asIso (targetMap p n)

@[reassoc (attr := simp)]
lemma relativeTargetIso_fst : (relativeTargetIso p n).hom ≫ (boundaryPullbackHom p n).fst =
    pullback.snd (reedyRestriction Y n) (reedyTargetMap p n) ≫ (matchingBoundaryIso Z n).inv := by
  simp only [relativeTargetIso, Iso.trans_hom, asIso_hom, targetMap, pullback.map,
    boundaryPullbackHom, Functor.PullbackObjObj.ofHasPullback_fst, Category.assoc,
    pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]

@[reassoc (attr := simp)]
lemma relativeTargetIso_snd : (relativeTargetIso p n).hom ≫ (boundaryPullbackHom p n).snd =
    pullback.fst (reedyRestriction Y n) (reedyTargetMap p n) := by
  simp only [relativeTargetIso, Iso.trans_hom, asIso_hom, targetMap, pullback.map,
    boundaryPullbackHom, Functor.PullbackObjObj.ofHasPullback_snd, Category.assoc,
    pullback.lift_snd, Category.comp_id, pullbackSymmetry_hom_comp_snd]

/-- Both source arrows agree under the concrete target isomorphism. -/
lemma relativeTargetIso_fac :
    relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
        (internalHomRight.map p) ≫ (relativeTargetIso p n).hom =
      (boundaryPullbackHom p n).π := by
  apply (boundaryPullbackHom p n).hom_ext
  · rw [Category.assoc, relativeTargetIso_fst, ← Category.assoc]
    rw [relativeMatchingMap_snd, Functor.PullbackObjObj.π_fst]
    exact matchingBoundaryIso_inv_restriction Z n
  · rw [Category.assoc, relativeTargetIso_snd]
    rw [relativeMatchingMap_fst, Functor.PullbackObjObj.π_snd]
    rfl

/-- The desired comparison is an isomorphism of actual arrows. -/
def relativeMatchingArrowIso :
    Arrow.mk (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p)) ≅ Arrow.mk (boundaryPullbackHom p n).π :=
  Arrow.isoMk (Iso.refl ((ihom (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n))).obj Z))
    (relativeTargetIso p n) (by
      change 𝟙 _ ≫ (boundaryPullbackHom p n).π =
        relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
          (internalHomRight.map p) ≫ (relativeTargetIso p n).hom
      exact (Category.id_comp _).trans (relativeTargetIso_fac p n).symm)

end SerrePositivity.BisimplicialModel
