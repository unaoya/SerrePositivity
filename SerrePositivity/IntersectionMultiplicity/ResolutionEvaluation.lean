module

public import SerrePositivity.HomologicalAlgebra.TorCochain
public import SerrePositivity.PerfectComplex.NormalizedEuler
public import Mathlib.Algebra.Ring.Action.Group
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Euler evaluation of a base-changed resolution

The cochain Euler evaluation, indexed by integers, agrees with the Tor Euler
evaluation, indexed by natural numbers, once negative-degree homology is
identified with Tor and positive degrees vanish. Coefficient extension is
compatible with composition. Neither Lemma 3.5 nor Tor symmetry is used.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R T C : Type u} [CommRing R] [CommRing T] [CommRing C]
variable {J : Ideal C} (lam : NormalizedLength C J)

/-- Reindex a cochain Euler evaluation by negative degrees and identify its
homology with Tor. This also respects the definitions' infinite-support values. -/
theorem lambdaEuler_eq_lambdaChi_of_homologyEquiv (φ : R →+* C)
    (M : Type u) [AddCommGroup M] [Module R M]
    (K : CochainComplex (ModuleCat.{u} C) ℤ)
    (hpos : ∀ i : ℤ, 0 < i → IsZero (K.X i))
    (e : ∀ i : ℕ, TorAlg φ i M ≃ₗ[C] K.homology (-(i : ℤ))) :
    lambdaEuler lam K = lambdaChi lam φ M := by
  let f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * (lam.len (K.homology i)).toReal
  let g := fun i : ℕ ↦ -(i : ℤ)
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    exact_mod_cast neg_injective hij
  have hs : Function.support f ⊆ Set.range g := by
    intro i hi
    have hnonpos : i ≤ 0 := by
      by_contra hn
      have hz : IsZero (K.homology i) :=
        (K.sc i).isZero_homology_of_isZero_X₂ (hpos i (by omega))
      have : Subsingleton (K.homology i) := ModuleCat.subsingleton_of_isZero hz
      exact hi (by simp [f, lam.len_eq_zero_of_subsingleton])
    refine ⟨(-i).toNat, ?_⟩
    dsimp [g]
    rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hfull : (∑ᶠ i ∈ Set.range g, f i) = ∑ᶠ i : ℤ, f i := by
    rw [← finsum_mem_inter_support f (Set.range g), Set.inter_eq_right.mpr hs,
      finsum_mem_support]
  change (∑ᶠ i : ℤ, f i) = _
  rw [← hfull, finsum_mem_range hg]
  unfold lambdaChi
  congr 1
  funext i
  have hlen := lam.len_congr _ _ (e i)
  simp only [f, g, Int.negOnePow_neg, Int.cast_negOnePow_natCast, hlen]

/-- Evaluate a coefficient extension using any cochain projective resolution. -/
theorem lambdaEuler_baseChange_resolution (φ : R →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M)) :
    lambdaEuler lam (baseChange φ F) = lambdaChi lam φ M :=
  lambdaEuler_eq_lambdaChi_of_homologyEquiv lam φ M (baseChange φ F)
    (baseChange_isZero_X_of_pos φ F hF.isZero_X)
    (fun i ↦ (torIsoCochain φ hF i).toLinearEquiv)

/-- Two coefficient extensions identify with extension along the composite. -/
noncomputable def baseChangeCompIso (φ : R →+* T) (ψ : T →+* C)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    baseChange ψ (baseChange φ F) ≅ baseChange (ψ.comp φ) F :=
  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm
    (ComplexShape.up ℤ)).app F

/-- Tor computed by successive coefficient extensions. -/
noncomputable def torAlgBaseChangeCompEquiv (φ : R →+* T) (ψ : T →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M))
    (i : ℕ) : TorAlg (ψ.comp φ) i M ≃ₗ[C]
      (baseChange ψ (baseChange φ F)).homology (-(i : ℤ)) :=
  ((torIsoCochain (ψ.comp φ) hF i) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (baseChangeCompIso φ ψ F).symm).toLinearEquiv

/-- The normalized Euler evaluation after two coefficient extensions is the
Tor Euler characteristic for their composite. -/
theorem chiLam_baseChange_resolution (φ : R →+* T) (ψ : T →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M)) :
    chiLam lam ψ (baseChange φ F) = lambdaChi lam (ψ.comp φ) M := by
  change lambdaEuler lam (baseChange ψ (baseChange φ F)) = _
  rw [lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso (baseChangeCompIso φ ψ F))]
  exact lambdaEuler_baseChange_resolution lam (ψ.comp φ) hF

/-- Restriction along an automorphism is extension along its inverse. This
orientation is the source of the inverse index in the norm comparison. -/
noncomputable def restrictScalarsIsoExtendInverse (σ : T ≃+* T) :
    ModuleCat.restrictScalars.{u} σ.toRingHom ≅ ModuleCat.extendScalars σ.symm.toRingHom :=
  Adjunction.leftAdjointUniq (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj σ.symm.toRingHom)

variable {G : Type u} [Group G] [MulSemiringAction G T]

/-- Twisting a base-changed complex changes its original coefficient map
by the inverse group element. -/
noncomputable def twistBaseChangeIso (φ : R →+* T) (g : G)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    twist g (baseChange φ F) ≅
      baseChange ((MulSemiringAction.toRingHom G T g⁻¹).comp φ) F := by
  let σ := MulSemiringAction.toRingEquiv G T g
  have he : σ.symm.toRingHom = MulSemiringAction.toRingHom G T g⁻¹ := by
    ext x
    rfl
  change ((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex _).obj
    (baseChange φ F) ≅ _
  refine (NatIso.mapHomologicalComplex (restrictScalarsIsoExtendInverse σ)
    (ComplexShape.up ℤ)).app
    (baseChange φ F) ≪≫ ?_
  simpa only [he] using baseChangeCompIso φ σ.symm.toRingHom F

/-- Tor identified with homology after twisting and successive coefficient
extensions. The second Tor variable is resolved throughout. -/
noncomputable def torAlgTwistBaseChangeEquiv (φ : R →+* T) (ψ : T →+* C) (g : G)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M))
    (i : ℕ) : TorAlg (ψ.comp ((MulSemiringAction.toRingHom G T g⁻¹).comp φ)) i M ≃ₗ[C]
      (baseChange ψ (twist g (baseChange φ F))).homology (-(i : ℤ)) :=
  ((torAlgBaseChangeCompEquiv ((MulSemiringAction.toRingHom G T g⁻¹).comp φ) ψ hF i).toModuleIso ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (((ModuleCat.extendScalars ψ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (twistBaseChangeIso φ g F).symm)).toLinearEquiv

/-- Normalized evaluation of a twisted resolution is the corresponding
Tor Euler evaluation with the inverse coefficient action. -/
theorem chiLam_twist_baseChange_resolution (φ : R →+* T) (ψ : T →+* C) (g : G)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M)) :
    chiLam lam ψ (twist g (baseChange φ F)) =
      lambdaChi lam (ψ.comp ((MulSemiringAction.toRingHom G T g⁻¹).comp φ)) M := by
  change lambdaEuler lam (baseChange ψ (twist g (baseChange φ F))) = _
  rw [lambdaEuler_eq_of_homotopyEquiv lam
    ((ModuleCat.extendScalars ψ).mapHomotopyEquiv (HomotopyEquiv.ofIso (twistBaseChangeIso φ g F)))]
  exact chiLam_baseChange_resolution lam ((MulSemiringAction.toRingHom G T g⁻¹).comp φ) ψ hF

end SerrePositivity
