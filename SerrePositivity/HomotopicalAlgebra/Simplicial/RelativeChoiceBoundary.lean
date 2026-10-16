module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryGluing
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceSpace

/-! # Filling prescribed compatible faces while retaining a fixed boundary

Face maps into the actual relative choice space are glued, then filled.
Every prescribed face is retained, and evaluating the filler keeps the
original V-boundary fixed throughout the entire higher simplex.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma fill_faces {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (n : ℕ)
    (f : ∀ k, (BoundaryGluing.facet n k).toSSet ⟶ obj i b) (hf : BoundaryGluing.Compatible f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ obj i b,
      (∀ k, (BoundaryGluing.facet n k).ι ≫ e = f k) ∧
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫ family i b e =
        V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ pointUnitIso.hom) ≫ (ρ_ V).hom ≫ b := by
  obtain ⟨e, he⟩ := extension hcof hfib i b p hp (SSet.boundary.{v} n).ι
    (BoundaryGluing.desc f hf)
  refine ⟨e, fun k => ?_, family_fixed_boundary i b e⟩
  have hk : SSet.boundary.faceι k ≫ (SSet.boundary.{v} n).ι = (BoundaryGluing.facet n k).ι := rfl
  rw [← hk, Category.assoc, he]
  exact BoundaryGluing.desc_fac f hf k

include hcof hfib in
/-- Fill given standard faces satisfying the ordinary simplicial face identities. -/
lemma fill_standard_faces {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (n : ℕ)
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ obj i b))
    (hf : BoundaryGluing.StandardCompatible f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 2)) ⟶ obj i b,
      (∀ k, SSet.stdSimplex.δ k ≫ e = f k) ∧
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 2)) ≫ family i b e =
        V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ pointUnitIso.hom) ≫ (ρ_ V).hom ≫ b := by
  obtain ⟨e, he⟩ := extension hcof hfib i b p hp (SSet.boundary.{v} (n + 2)).ι
    (BoundaryGluing.standardDesc f hf)
  refine ⟨e, fun k => ?_, family_fixed_boundary i b e⟩
  rw [← SSet.boundary.ι_ι k, Category.assoc, he]
  exact BoundaryGluing.standardDesc_fac f hf k

end SerrePositivity.SimplicialModel.RelativeChoiceSpace
