module
public import SerrePositivity.HomologicalAlgebra.ArtinReesHomology
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleConeNaturality
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Ideal-adic depth of actual Koszul power transitions -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber DerivedCompletion
variable {R : Type u} [CommRing R]

/-- If both diagonal entries have image in I, so does the actual cone-map component. -/
lemma moduleConeArrowMap_range_le_ideal_smul
    {P Q P' Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : P ⟶ Q) (ψ : P' ⟶ Q') (α : Arrow.mk φ ⟶ Arrow.mk ψ)
    (I : Ideal R) (q : ℤ)
    (hleft : LinearMap.range (α.left.f (q + 1)).hom ≤ I • ⊤)
    (hright : LinearMap.range (α.right.f q).hom ≤ I • ⊤) :
    LinearMap.range
      ((mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q).hom ≤ I • ⊤ := by
  rintro _ ⟨x, rfl⟩
  let f := (mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q
  have hx : inlX φ (q + 1) q rfl (fstX φ q (q + 1) rfl x) +
      inrX φ q (sndX φ q x) = x :=
    congrArg (fun g => g x) (moduleCone_coordinates_total φ q (q + 1) rfl)
  change f x ∈ I • ⊤
  rw [← hx, map_add]
  have h₁ := congrArg (fun g => g (fstX φ q (q + 1) rfl x))
    (moduleConeArrowMap_inl φ ψ α q (q + 1) rfl)
  have h₂ := congrArg (fun g => g (sndX φ q x))
    (moduleConeArrowMap_inr φ ψ α q)
  apply Submodule.add_mem
  · rw [show f (inlX φ (q + 1) q rfl (fstX φ q (q + 1) rfl x)) =
      inlX ψ (q + 1) q rfl (α.left.f (q + 1) (fstX φ q (q + 1) rfl x)) from h₁]
    exact Submodule.smul_top_le_comap_smul_top I (inlX ψ (q + 1) q rfl).hom
      (hleft (LinearMap.mem_range_self _ _))
  · rw [show f (inrX φ q (sndX φ q x)) =
      inrX ψ q (α.right.f q (sndX φ q x)) from h₂]
    exact Submodule.smul_top_le_comap_smul_top I (inrX ψ q).hom
      (hright (LinearMap.mem_range_self _ _))

/-- When all multipliers lie in I, a Koszul coordinate map has image in I in negative degrees. -/
lemma koszulComplexMapOfMul_negative_range_le_ideal_smul :
    ∀ {e : ℕ} (a b c : Fin e → R) (h : ∀ j, a j = b j * c j)
      (I : Ideal R) (_hc : ∀ j, c j ∈ I) (q : ℤ), q < 0 →
      LinearMap.range ((koszulComplexMapOfMul R a b c h).f q).hom ≤ I • ⊤ := by
  intro e
  induction e with
  | zero =>
    intro a b c h I hc q hq
    have hz := koszulComplex_isZero_X_of_lt b q (by simpa using hq)
    have hzero : (koszulComplexMapOfMul R a b c h).f q = 0 := hz.eq_of_tgt _ _
    simp [hzero]
  | succ e ih =>
    intro a b c h I hc q hq
    apply moduleConeArrowMap_range_le_ideal_smul
    · rintro _ ⟨x, rfl⟩
      change c (Fin.last e) •
        (koszulComplexMapOfMul R (Fin.init a) (Fin.init b) (Fin.init c)
          (fun j => h j.castSucc)).f (q + 1) x ∈ I • ⊤
      exact Submodule.smul_mem_smul (hc (Fin.last e)) Submodule.mem_top
    · exact ih (Fin.init a) (Fin.init b) (Fin.init c) (fun j => h j.castSucc)
        I (fun j => hc j.castSucc) q hq

/-- Every adjacent power transition has image in the parameter ideal in negative degrees. -/
lemma powerKoszulTransition_negative_range_le_span {e : ℕ} (z : Fin e → R)
    (n : ℕ) (q : ℤ) (hq : q < 0) :
    LinearMap.range ((powerKoszulTransition R z n).f q).hom ≤
      Ideal.span (Set.range z) • ⊤ :=
  koszulComplexMapOfMul_negative_range_le_ideal_smul _ _ _ _ _
    (fun j => Ideal.subset_span (Set.mem_range_self j)) q hq

/-- Ideal-adic depths add when linear maps are composed. -/
lemma linearMap_range_comp_le_pow_smul_top
    {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (I : Ideal R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) (a b : ℕ)
    (hf : LinearMap.range f ≤ I ^ a • ⊤) (hg : LinearMap.range g ≤ I ^ b • ⊤) :
    LinearMap.range (g.comp f) ≤ I ^ (a + b) • ⊤ := by
  rw [LinearMap.range_comp]
  calc
    Submodule.map g (LinearMap.range f) ≤ Submodule.map g (I ^ a • ⊤) :=
      Submodule.map_mono hf
    _ = I ^ a • LinearMap.range g := by rw [Submodule.map_smul'', Submodule.map_top]
    _ ≤ I ^ a • (I ^ b • ⊤) := Submodule.smul_mono le_rfl hg
    _ = I ^ (a + b) • ⊤ := by rw [← Submodule.mul_smul, ← pow_add]

/-- The actual inverse sequence obtained by composing the original adjacent power transitions. -/
def powerKoszulInverseDiagram {e : ℕ} (z : Fin e → R) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  Functor.ofOpSequence (powerKoszulTransition R z)

/-- A k-step original power transition has image in the k-th parameter-ideal power. -/
lemma powerKoszulInverseDiagram_negative_range_le_span_pow {e : ℕ} (z : Fin e → R)
    (n k : ℕ) (q : ℤ) (hq : q < 0) :
    LinearMap.range (((powerKoszulInverseDiagram z).map
      (homOfLE (show n ≤ n + k by omega)).op).f q).hom ≤
        Ideal.span (Set.range z) ^ k • ⊤ := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have heq : (homOfLE (show n ≤ n + (k + 1) by omega)).op =
        (homOfLE (show n + k ≤ n + k + 1 by omega)).op ≫
          (homOfLE (show n ≤ n + k by omega)).op := Subsingleton.elim _ _
    rw [heq, Functor.map_comp]
    change LinearMap.range
      ((((powerKoszulInverseDiagram z).map (homOfLE (show n ≤ n + k by omega)).op).f q).hom.comp
        (((powerKoszulInverseDiagram z).map
          (homOfLE (show n + k ≤ n + k + 1 by omega)).op).f q).hom) ≤ _
    apply le_trans (linearMap_range_comp_le_pow_smul_top
      (Ideal.span (Set.range z)) _ _ 1 k _ ih)
    · simp [Nat.add_comm]
    · simpa only [powerKoszulInverseDiagram, Functor.ofOpSequence_map_homOfLE_succ, pow_one]
        using powerKoszulTransition_negative_range_le_span z (n + k) q hq

/-- Arbitrary parameter sequences over Noetherian rings have pro-zero positive Koszul homology,
for the actual inverse system of power transitions. -/
lemma powerKoszul_negative_homology_proZero [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (q : ℤ) (hq : q < 0) (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n ≤ m,
      homologyMap ((powerKoszulInverseDiagram z).map (homOfLE hnm).op) q = 0 := by
  obtain ⟨k, hk⟩ := powerKoszul_homologyMap_eq_zero_of_deep_image z n q
  exact ⟨n + k, by omega, hk _ _
    (powerKoszulInverseDiagram_negative_range_le_span_pow z n k q hq)⟩

end SerrePositivity
