module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ProductBoundaryCotensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveProductParameter

/-! # Gluing all whole facet systems with a moving parameter and moving values -/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.SimplicialModel.NerveCylinderBoundary
open SerrePositivity.SimplicialModel.NerveBiparameterMaps

namespace SerrePositivity.SimplicialModel.NerveMovingBoundary
variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{w}) {n : ℕ}

abbrev Compatible (faces : Fin (n + 3) → NerveBiparameter.System
    (product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) F) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    faces j ≫ restriction _ _ F (vertical (SSet.stdSimplex.δ
      (k.pred (Fin.ne_zero_of_lt hjk))) K) =
    faces k ≫ restriction _ _ F (vertical (SSet.stdSimplex.δ
      (j.castPred (Fin.ne_last_of_lt hjk))) K)

variable (faces : Fin (n + 3) → NerveBiparameter.System
    (product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) F)
  (hf : Compatible K F faces)

include hf in
lemma component_compatible (s : Index D) :
    ProductBoundaryCotensor.Compatible (fun k => (faces k).app s) := by
  intro j k hjk
  exact congr_app (hf j k hjk) s

/-- Glue the actual boundary product, keeping all whole facets in every external degree. -/
def boundary : NerveBiparameter.System (product K (SSet.boundary (n + 2)).toSSet) F where
  app s := ProductBoundaryCotensor.standardDesc (fun k => (faces k).app s)
    (component_compatible K F faces hf s)
  naturality {s t} f := by
    apply ProductBoundaryCotensor.hom_ext
    intro k
    simp only [Category.assoc, ProductBoundaryCotensor.standardDesc_fac]
    have hn := (restriction (product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1))))
      (product K (SSet.boundary (n + 2)).toSSet) F (vertical (SSet.boundary.ι k) K)).naturality f
    rw [restriction_app, restriction_app] at hn
    have hg := ProductBoundaryCotensor.standardDesc_fac (fun k => (faces k).app s)
      (component_compatible K F faces hf s) k
    exact ((faces k).naturality f).trans
      ((congrArg (fun a => a ≫ (NerveBiparameter.values
        (product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) F).map f) hg.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (fun a => ProductBoundaryCotensor.standardDesc
          (fun k => (faces k).app s) (component_compatible K F faces hf s) ≫ a) hn.symm)))

lemma boundary_face (k : Fin (n + 3)) : boundary K F faces hf ≫ restriction _ _ F
    (vertical (SSet.boundary.ι k) K) = faces k := by
  apply NatTrans.ext
  funext s
  exact ProductBoundaryCotensor.standardDesc_fac (fun k => (faces k).app s)
    (component_compatible K F faces hf s) k

lemma hom_ext {m : ℕ}
    {a b : NerveBiparameter.System (product K (SSet.boundary (m + 1)).toSSet) F}
    (h : ∀ k : Fin (m + 2), a ≫ restriction _ _ F (vertical (SSet.boundary.ι k) K) =
      b ≫ restriction _ _ F (vertical (SSet.boundary.ι k) K)) : a = b := by
  apply NatTrans.ext
  funext s
  apply ProductBoundaryCotensor.hom_ext
  intro k
  exact congr_app (h k) s

end SerrePositivity.SimplicialModel.NerveMovingBoundary
