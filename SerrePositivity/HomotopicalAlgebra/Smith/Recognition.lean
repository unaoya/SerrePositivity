module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic

public import SerrePositivity.HomotopicalAlgebra.Smith.GeneratingTrivialCofibrations
public import SerrePositivity.HomotopicalAlgebra.Transfer.Recognition

/-! # Lifting and recognition from Smith solution squares

The first lemmas isolate the algebraic recognition argument from the separate
closure and completeness arguments needed for the final Smith theorem.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C] (I J W : MorphismProperty C)

/-- Square factorization upgrades J-injectivity of a weak equivalence to I-injectivity. -/
lemma rlp_inf_le_of_square_factor
    (hfactor : ∀ (i f : Arrow C), I i.hom → W f.hom → ∀ sq : i ⟶ f,
      ∃ g : Arrow C, J g.hom ∧ ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq) :
    J.rlp ⊓ W ≤ I.rlp := by
  intro X Y f hf A B i hi
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨g, hg, p, q, hpq⟩ := hfactor (Arrow.mk i) (Arrow.mk f) hi hf.2
    (Arrow.homMk a b sq.w)
  have : HasLiftingProperty g.hom f := hf.1 _ hg
  let qs : CommSq q.left g.hom f q.right := ⟨q.w⟩
  have hl := congrArg Arrow.Hom.left hpq
  have hr := congrArg Arrow.Hom.right hpq
  have pw : p.left ≫ g.hom = i ≫ p.right := p.w
  exact ⟨⟨{
    l := p.right ≫ qs.lift
    fac_left := by
      rw [← Category.assoc, ← pw, Category.assoc, qs.fac_left]
      exact hl
    fac_right := by
      rw [Category.assoc, qs.fac_right]
      exact hr
  }⟩⟩

lemma rlp_eq_of_square_factor (hJ : J ≤ I.rlp.llp) (hIW : I.rlp ≤ W)
    (hfactor : ∀ (i f : Arrow C), I i.hom → W f.hom → ∀ sq : i ⟶ f,
      ∃ g : Arrow C, J g.hom ∧ ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq) :
    I.rlp = J.rlp ⊓ W := by
  apply le_antisymm
  · intro X Y f hf
    exact ⟨fun A B j hj ↦ hJ _ hj _ hf, hIW _ hf⟩
  · exact rlp_inf_le_of_square_factor I J W hfactor

/-- The retract argument, with acyclicity exposed until its closure proof is supplied. -/
lemma generatedLeft_eq_of_square_factor
    [J.HasSmallObjectArgument.{w}] [W.HasTwoOutOfThreeProperty]
    (hJ : J ≤ I.rlp.llp) (hIW : I.rlp ≤ W)
    (hfactor : ∀ (i f : Arrow C), I i.hom → W f.hom → ∀ sq : i ⟶ f,
      ∃ g : Arrow C, J g.hom ∧ ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq)
    (hacyclic : J.rlp.llp ≤ W) : J.rlp.llp = I.rlp.llp ⊓ W := by
  have heq := rlp_eq_of_square_factor I J W hJ hIW hfactor
  apply le_antisymm
  · intro X Y f hf
    refine ⟨?_, hacyclic _ hf⟩
    apply MorphismProperty.antitone_llp (show I.rlp ≤ J.rlp from ?_) _ hf
    exact fun _ _ _ h ↦ (heq ▸ h).1
  · intro X Y f hf
    let fac := MorphismProperty.factorizationData J.rlp.llp J.rlp f
    have hpW : W fac.p := W.of_precomp fac.i fac.p (hacyclic _ fac.hi)
      (by simpa using hf.2)
    have hpI : I.rlp fac.p := heq.symm ▸ ⟨fac.hp, hpW⟩
    have : HasLiftingProperty f fac.p := hf.1 _ hpI
    exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty fac.fac) fac.hi

/-- Closure under coproducts, cobase change and transfinite composition is sufficient
for cell acyclicity. The coproduct hypothesis will be discharged separately from
the weaker closure assumptions of Smith's theorem. -/
lemma generatedLeft_le_of_closure
    [J.HasSmallObjectArgument.{w}] [W.IsStableUnderRetracts]
    [(I.rlp.llp ⊓ W).IsStableUnderCoproducts.{w}]
    [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
    [(I.rlp.llp ⊓ W).IsStableUnderTransfiniteComposition.{w}]
    (hJ : J ≤ I.rlp.llp ⊓ W) : J.rlp.llp ≤ I.rlp.llp ⊓ W := by
  apply ModelGeneration.generatedLeft_le_of_cells_le J (I.rlp.llp ⊓ W)
  apply le_trans (MorphismProperty.transfiniteCompositions_monotone ?_)
    (I.rlp.llp ⊓ W).transfiniteCompositions_le
  apply le_trans (MorphismProperty.pushouts_monotone ?_) (I.rlp.llp ⊓ W).pushouts_le
  exact (MorphismProperty.coproducts_monotone hJ).trans (I.rlp.llp ⊓ W).coproducts_le

/-- Conditional algebraic core on the caller's Mathlib classes. Completeness and
acyclicity remain explicit here; this lemma alone is not full Smith recognition. -/
@[instance_reducible]
def modelCategoryOfSquareFactor
    [I.HasSmallObjectArgument.{w}] [J.HasSmallObjectArgument.{w}]
    [CategoryWithCofibrations C] [CategoryWithFibrations C]
    [CategoryWithWeakEquivalences C]
    [CategoryTheory.Limits.HasFiniteLimits C] [CategoryTheory.Limits.HasFiniteColimits C]
    [W.HasTwoOutOfThreeProperty]
    (hC : cofibrations C = I.rlp.llp) (hF : fibrations C = J.rlp)
    (hW : weakEquivalences C = W)
    (hJ : J ≤ I.rlp.llp) (hIW : I.rlp ≤ W)
    (hfactor : ∀ (i f : Arrow C), I i.hom → W f.hom → ∀ sq : i ⟶ f,
      ∃ g : Arrow C, J g.hom ∧ ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq)
    (hacyclic : J.rlp.llp ≤ W) : ModelCategory C := by
  have : (weakEquivalences C).HasTwoOutOfThreeProperty := hW.symm ▸ inferInstance
  apply ModelGeneration.modelCategoryOfRecognition I J
  · rw [trivialFibrations, hF, hW]
    exact rlp_eq_of_square_factor I J W hJ hIW hfactor
  · exact hF.symm
  · exact hC
  · exact hW.symm ▸ hacyclic

/-- Cofibrant generation on the recognized Mathlib model structure. -/
lemma cofibrantlyGeneratedOfSquareFactor
    [ModelCategory C] [I.HasSmallObjectArgument.{w}] [J.HasSmallObjectArgument.{w}]
    (hF : fibrations C = J.rlp) (hW : weakEquivalences C = W)
    (hJ : J ≤ I.rlp.llp) (hIW : I.rlp ≤ W)
    (hfactor : ∀ (i f : Arrow C), I i.hom → W f.hom → ∀ sq : i ⟶ f,
      ∃ g : Arrow C, J g.hom ∧ ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J where
  smallObjectI := inferInstance
  smallObjectJ := inferInstance
  rlp_I := by
    rw [trivialFibrations, hF, hW]
    exact rlp_eq_of_square_factor I J W hJ hIW hfactor
  rlp_J := hF.symm

end SerrePositivity.Smith
