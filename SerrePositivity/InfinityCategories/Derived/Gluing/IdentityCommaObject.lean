module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismConstantInput
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaCategory

/-! 恒等 augmentation の実 comma 対象と、その全定値入力での prism。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

abbrev dgGluingIdentityCommaObject (x : E) : DGFunctorCommaObject R E E (DGFunctor.id E) where
  source := x
  replacement := x
  augmentation := 𝟙 (ForgetEnrichment.of (Complex R) x)

lemma dgGluingClosedIdentityEdge (x : E) :
    (dgClosedEdge R E (𝟙 (ForgetEnrichment.of (Complex R) x))).edge =
      InfinityCategories.PinchedHom.constant (X := dgNerve R E) (Simplex.vertex x) 1 := by
  have h := edgeOfCycle_edgeCycle
    (Truncated.Edge.id (X := (truncation 2).obj (dgNerve R E)) (Simplex.vertex x))
  rw [edgeCycle_id] at h
  rw [dgClosedEdge, closedHom_id]
  exact (congrArg (fun e => e.edge) h).trans (pinchedConstant_one (X := dgNerve R E) _).symm

lemma dgGluingIdentityCommaPrism_constant (x : E) {n : ℕ} (β : Fin (n + 1) →o Fin 2) :
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (InfinityCategories.PinchedHom.constant
        (X := dgNerve R (DGFunctorCommaObject R E E (DGFunctor.id E)))
        (Simplex.vertex (dgGluingIdentityCommaObject R E x)) n) β =
      InfinityCategories.PinchedHom.constant (X := dgNerve R E) (Simplex.vertex x) n := by
  rw [dgGluingCommaPrism_constant_input]
  change (dgClosedEdge R E (𝟙 (ForgetEnrichment.of (Complex R) x))).edge.pullback β = _
  rw [dgGluingClosedIdentityEdge]
  exact InfinityCategories.PinchedHom.constant_pullback (X := dgNerve R E) (Simplex.vertex x)
    (SimplexCategory.mkHom β)

end SerrePositivity.InfinityCategories
