module
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Cokernel dimension shifting for exact coefficient complexes

The connecting map in a short exact sequence is a cokernel whenever the next
homology of the middle complex vanishes. This includes degree zero.
-/
@[expose] public noncomputable section
universe v u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℕ)} (hS : S.ShortExact) (n : ℕ)

/-- Acyclicity of the middle term in the next degree makes the connecting map epic. -/
lemma coefficientDimensionShift_epi
    (h : IsZero (S.X₂.homology (n + 1))) : Epi (hS.δ n (n + 1) rfl) := by
  exact (hS.homology_exact₁ n (n + 1) rfl).epi_f (h.eq_zero_of_tgt _)

/-- The connecting map is the actual cokernel of the preceding homology map. -/
def coefficientDimensionShiftIsCokernel
    (h : IsZero (S.X₂.homology (n + 1))) :
    IsColimit (CokernelCofork.ofπ (hS.δ n (n + 1) rfl)
      (hS.comp_δ n (n + 1) rfl)) := by
  have := coefficientDimensionShift_epi hS n h
  exact (hS.homology_exact₃ n (n + 1) rfl).gIsCokernel

/-- A compatible comparison of the two preceding homology objects determines
an isomorphism in the next degree. -/
def coefficientDimensionShiftIso
    {T : ShortComplex (CochainComplex C ℕ)} (hT : T.ShortExact)
    (h : IsZero (S.X₂.homology (n + 1)))
    (h' : IsZero (T.X₂.homology (n + 1)))
    (e₂ : S.X₂.homology n ≅ T.X₂.homology n)
    (e₃ : S.X₃.homology n ≅ T.X₃.homology n)
    (w : homologyMap S.g n ≫ e₃.hom = e₂.hom ≫ homologyMap T.g n) :
    S.X₁.homology (n + 1) ≅ T.X₁.homology (n + 1) :=
  CokernelCofork.mapIsoOfIsColimit
    (coefficientDimensionShiftIsCokernel hS n h)
    (coefficientDimensionShiftIsCokernel hT n h')
    (Arrow.isoMk e₂ e₃ w.symm)

/-- The lifted comparison commutes with the actual connecting morphism. -/
@[reassoc]
lemma coefficientDimensionShiftIso_δ
    {T : ShortComplex (CochainComplex C ℕ)} (hT : T.ShortExact)
    (h : IsZero (S.X₂.homology (n + 1)))
    (h' : IsZero (T.X₂.homology (n + 1)))
    (e₂ : S.X₂.homology n ≅ T.X₂.homology n)
    (e₃ : S.X₃.homology n ≅ T.X₃.homology n)
    (w : homologyMap S.g n ≫ e₃.hom = e₂.hom ≫ homologyMap T.g n) :
    hS.δ n (n + 1) rfl ≫ (coefficientDimensionShiftIso hS n hT h h' e₂ e₃ w).hom =
      e₃.hom ≫ hT.δ n (n + 1) rfl := by
  exact CokernelCofork.π_mapOfIsColimit
    (coefficientDimensionShiftIsCokernel hS n h)
    (CokernelCofork.ofπ (hT.δ n (n + 1) rfl) (hT.comp_δ n (n + 1) rfl))
    (Arrow.isoMk e₂ e₃ w.symm).hom

/-- A comparison commuting with the connecting maps is uniquely determined. -/
lemma coefficientDimensionShift_unique
    (h : IsZero (S.X₂.homology (n + 1))) {X : C}
    (f g : S.X₁.homology (n + 1) ⟶ X)
    (w : hS.δ n (n + 1) rfl ≫ f = hS.δ n (n + 1) rfl ≫ g) : f = g := by
  have := coefficientDimensionShift_epi hS n h
  exact (cancel_epi (hS.δ n (n + 1) rfl)).mp w

/-- Naturality of lifted comparisons follows from naturality one degree below.
The two short-exact-sequence maps may come from different choices of injective
embeddings; only their actual third-component homology square is required. -/
lemma coefficientDimensionShift_naturality
    {S' T T' : ShortComplex (CochainComplex C ℕ)}
    (hS' : S'.ShortExact) (hT : T.ShortExact) (hT' : T'.ShortExact)
    (h : IsZero (S.X₂.homology (n + 1)))
    (f : S ⟶ S') (g : T ⟶ T')
    (e : S.X₁.homology (n + 1) ⟶ T.X₁.homology (n + 1))
    (e' : S'.X₁.homology (n + 1) ⟶ T'.X₁.homology (n + 1))
    (q : S.X₃.homology n ⟶ T.X₃.homology n)
    (q' : S'.X₃.homology n ⟶ T'.X₃.homology n)
    (he : hS.δ n (n + 1) rfl ≫ e = q ≫ hT.δ n (n + 1) rfl)
    (he' : hS'.δ n (n + 1) rfl ≫ e' = q' ≫ hT'.δ n (n + 1) rfl)
    (hq : homologyMap f.τ₃ n ≫ q' = q ≫ homologyMap g.τ₃ n) :
    homologyMap f.τ₁ (n + 1) ≫ e' = e ≫ homologyMap g.τ₁ (n + 1) := by
  apply coefficientDimensionShift_unique hS n h
  calc
    _ = (homologyMap f.τ₃ n ≫ hS'.δ n (n + 1) rfl) ≫ e' := by
      rw [← Category.assoc, HomologySequence.δ_naturality f hS hS' n (n + 1) rfl]
    _ = (q ≫ homologyMap g.τ₃ n) ≫ hT'.δ n (n + 1) rfl := by
      rw [Category.assoc, he', ← Category.assoc, hq]
    _ = (q ≫ hT.δ n (n + 1) rfl) ≫ homologyMap g.τ₁ (n + 1) := by
      rw [Category.assoc, ← HomologySequence.δ_naturality g hT hT' n (n + 1) rfl,
        ← Category.assoc]
    _ = _ := by rw [← he, Category.assoc]

end SerrePositivity
