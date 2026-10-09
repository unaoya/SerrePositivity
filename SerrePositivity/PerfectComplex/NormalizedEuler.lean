module

public import SerrePositivity.HomologicalAlgebra.ConeLES
public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.PerfectComplex.K0
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Euler evaluation for an abstract additive length

`lambdaEuler lam P = Σ_i (-1)^i λ H^i(P)` for a normalized length `λ`. Finite normalized
homology lengths and power torsion suffice for homotopy invariance and mapping-cone
additivity. No Noetherian hypothesis on the coefficient ring is used.

The ordinary length is the normalized length `NormalizedLength.ordinary` for `J = ⊥`, so the
ordinary Euler evaluation `chiOrd` is the special case `chiOrd_eq_lambdaEuler_ordinary`; the
ordinary statements are derived from the ones here in `OrdinaryEuler.lean`.

The last section descends the normalized evaluation `chiLam` of supported perfect complexes to
the supported `K₀`, assuming the homology lengths are finite (`chiLamHom_of_finite`). The
finiteness itself is the Koszul argument of Lemma 3.5a (`Paper/Lemma3_5/A_Normalized.lean`).
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

section general

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- Euler evaluation of a coefficient-ring complex by the abstract length. -/
noncomputable def lambdaEuler (P : CochainComplex (ModuleCat.{u} C) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (P.homology i)).toReal

/-- Exactness expresses the length of the middle term as the sum of image lengths. -/
lemma lambdaLengthReal_eq_add_range {M N L : Type u} [AddCommGroup M] [Module C M]
    [AddCommGroup N] [Module C N] [AddCommGroup L] [Module C L]
    (f : M →ₗ[C] N) (g : N →ₗ[C] L) (hfg : Function.Exact f g)
    (tN : IsPowTorsion J N) (hN : lam.len N ≠ ⊤) :
    (lam.len N).toReal = (lam.len (LinearMap.range f)).toReal +
      (lam.len (LinearMap.range g)).toReal := by
  have hk : lam.len (LinearMap.ker g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (lam.len_submodule_le tN _)
  have hr : lam.len (LinearMap.range g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (lam.len_range_le g tN)
  rw [lam.len_eq_add_ker_range g tN, ENNReal.toReal_add hk hr,
    ← LinearMap.exact_iff.mp hfg]

/-- Boundedness makes the homology evaluation finitely supported. -/
lemma lambdaHomology_hasFiniteSupport (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    Function.HasFiniteSupport (fun i ↦ (lam.len (P.homology i)).toReal) := by
  obtain ⟨a, b, hab⟩ := hP
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hn
  have hzero : IsZero (P.homology i) :=
    (P.sc i).isZero_homology_of_isZero_X₂ (hab i (by simp only [Set.mem_Icc] at hn; omega))
  have := ModuleCat.subsingleton_of_isZero hzero
  exact hi (by simp [lam.len_eq_zero_of_subsingleton])

/-- Homotopy equivalent coefficient complexes have the same evaluation. -/
lemma lambdaEuler_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : HomotopyEquiv P Q) : lambdaEuler lam P = lambdaEuler lam Q := by
  unfold lambdaEuler
  congr 1
  funext i
  rw [lam.len_congr _ _ (h.toHomologyIso i).toLinearEquiv]

private lemma alternating_finsum_shift (f : ℤ → ℝ) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f (i - 1)) =
      -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f i) := by
  calc
    _ = ∑ᶠ i : ℤ, (((i + 1).negOnePow : ℤ) : ℝ) * f i := by
      have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * f (i - 1))
      simpa using h.symm
    _ = ∑ᶠ i : ℤ, -(((i.negOnePow : ℤ) : ℝ) * f i) := by
      congr 1
      funext i
      simp [Int.negOnePow_add]
    _ = _ := finsum_neg_distrib _

set_option maxHeartbeats 800000 in
-- Transporting the three exact sequences with dependent homology objects
-- requires additional elaboration time.
/-- The Euler evaluation is additive on a mapping-cone triangle when
the homology is bounded, power torsion, and has finite length. -/
theorem lambdaEuler_cone {P Q : CochainComplex (ModuleCat.{u} C) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (tP : ∀ i, IsPowTorsion J (P.homology i))
    (tQ : ∀ i, IsPowTorsion J (Q.homology i))
    (tC : ∀ i, IsPowTorsion J ((Cone.cone f).homology i))
    (lP : ∀ i, lam.len (P.homology i) ≠ ⊤)
    (lQ : ∀ i, lam.len (Q.homology i) ≠ ⊤)
    (lC : ∀ i, lam.len ((Cone.cone f).homology i) ≠ ⊤) :
    lambdaEuler lam (Cone.cone f) = lambdaEuler lam Q - lambdaEuler lam P := by
  let α := fun i ↦ (HomologicalComplex.homologyMap f i).hom
  let β := fun i ↦ (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i).hom
  let δ := fun i ↦ (Cone.δ f i (i + 1) rfl).hom
  let a := fun i ↦ (lam.len (LinearMap.range (α i))).toReal
  let b := fun i ↦ (lam.len (LinearMap.range (β i))).toReal
  let d := fun i ↦ (lam.len (LinearMap.range (δ i))).toReal
  have ha : Function.HasFiniteSupport a := by
    apply (lambdaHomology_hasFiniteSupport lam Q hQ).subset
    intro i hi hz
    have hz' : lam.len (Q.homology i) = 0 := by
      have hn := lQ i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (α i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_submodule_le (tQ i) _) bot_le
    exact hi (by simp [a, this])
  have hb : Function.HasFiniteSupport b := by
    apply (lambdaHomology_hasFiniteSupport lam (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : lam.len ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (β i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_submodule_le (tC i) _) bot_le
    exact hi (by simp [b, this])
  have hd : Function.HasFiniteSupport d := by
    apply (lambdaHomology_hasFiniteSupport lam (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : lam.len ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (δ i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_range_le (δ i) (tC i)) bot_le
    exact hi (by simp [d, this])
  have hQlen : ∀ i, ((lam.len (Q.homology i)).toReal : ℝ) = a i + b i := fun i ↦
    lambdaLengthReal_eq_add_range lam (α i) (β i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₂ f i)) (tQ i) (lQ i)
  have hClen : ∀ i, ((lam.len ((Cone.cone f).homology i)).toReal : ℝ) = b i + d i := fun i ↦
    lambdaLengthReal_eq_add_range lam (β i) (δ i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₃ f i (i + 1) rfl)) (tC i) (lC i)
  have hPlen : ∀ i, ((lam.len (P.homology i)).toReal : ℝ) = d (i - 1) + a i := by
    intro i
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact lambdaLengthReal_eq_add_range lam (δ j) (α (j + 1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₁ f j (j + 1) rfl)) (tP (j + 1)) (lP (j + 1))
  have haw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * a i) :=
    ha.mul_right _
  have hbw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * b i) :=
    hb.mul_right _
  have hdw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * d i) :=
    hd.mul_right _
  have hds : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * d (i - 1)) := by
    have hdp : Function.HasFiniteSupport (fun i : ℤ ↦ d (i - 1)) :=
      hd.preimage (Equiv.subRight (1 : ℤ)).injective.injOn
    exact hdp.mul_right _
  have eQ : lambdaEuler lam Q = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) := by
    simp_rw [lambdaEuler, hQlen, mul_add]
    exact finsum_add_distrib haw hbw
  have eC : lambdaEuler lam (Cone.cone f) = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) := by
    simp_rw [lambdaEuler, hClen, mul_add]
    exact finsum_add_distrib hbw hdw
  have eP : lambdaEuler lam P = -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) := by
    simp_rw [lambdaEuler, hPlen, mul_add]
    rw [finsum_add_distrib hds haw, alternating_finsum_shift]
  rw [eC, eQ, eP]
  ring

/-- Supported homology belongs to the power-torsion category. -/
lemma supported_homology_isPowTorsion (hfg : J.FG) {n : ℕ}
    {w : Fin n → C} (hJ : J ≤ (Ideal.span (Set.range w)).radical)
    {P : CochainComplex (ModuleCat.{u} C) ℤ} (hP : IsSupported w P) (i : ℤ) :
    IsPowTorsion J (P.homology i) := by
  have hAnn : J ≤ (Module.annihilator C (P.homology i)).radical :=
    hJ.trans (by
      have h := Ideal.radical_mono (hP.le_radical_annihilator i)
      simpa only [Ideal.radical_idem] using h)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hAnn hfg
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  exact hn

/-! ## The ordinary length as a normalized length -/

/-- Casting `ℕ∞` into `ℝ≥0∞` and then into `ℝ` agrees with `ENat.toNat`; both send `⊤` to `0`. -/
lemma toReal_toENNReal (n : ℕ∞) : (n : ℝ≥0∞).toReal = (n.toNat : ℝ) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k => simp

/-- The ordinary Euler evaluation is the one for `NormalizedLength.ordinary`. -/
lemma chiOrd_eq_lambdaEuler_ordinary {T : Type u} [CommRing T]
    (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    chiOrd P = lambdaEuler (NormalizedLength.ordinary T) P := by
  unfold chiOrd lambdaEuler
  simp only [NormalizedLength.ordinary_len, toReal_toENNReal]

end general

/-! ## Normalized Euler evaluation on supported perfect complexes

Over a tower `A → T → C` with `z` a tuple in `A` generating an `m_A`-primary ideal and `λ` a
normalized length on `C` for the ideal `m_A C`, the homology of the base change to `C` of a
`z`-supported perfect `T`-complex lies in the domain of `λ`. When these lengths are finite,
`chiLam lam` descends to `K₀^{m_A}(T)`. -/

section supported

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

/-- Base-changed supported complexes have homology in the domain of `λ`. -/
lemma chiLam_homology_isPowTorsion
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    {P : CochainComplex (ModuleCat.{u} T) ℤ}
    (hP : IsPerfectSupported (algebraMap A T ∘ z) P) (i : ℤ) :
    IsPowTorsion ((maximalIdeal A).map (algebraMap A C))
      ((baseChange (algebraMap T C) P).homology i) := by
  have hfg := (maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C)
  have hJ : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap A C ∘ z))).radical := by
    have h := Ideal.map_radical_le (algebraMap A C) (I := Ideal.span (Set.range z))
    rw [hz, Ideal.map_span, ← Set.range_comp] at h
    exact h
  have hs : IsSupported (algebraMap A C ∘ z) (baseChange (algebraMap T C) P) := by
    have h := isSupported_baseChange (algebraMap T C) hP.supported
    have heq : algebraMap T C ∘ (algebraMap A T ∘ z) = algebraMap A C ∘ z := by
      funext j
      exact (IsScalarTower.algebraMap_apply A T C (z j)).symm
    rwa [heq] at h
  exact supported_homology_isPowTorsion hfg hJ hs i

omit [IsNoetherianRing A] [Algebra A T] [Algebra T C] [IsScalarTower A T C] in
/-- Normalized Euler evaluation is invariant under homotopy equivalence. -/
lemma chiLam_eq_of_homotopyEquiv (φ : T →+* C)
    {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (h : HomotopyEquiv P Q) :
    chiLam lam φ P = chiLam lam φ Q :=
  lambdaEuler_eq_of_homotopyEquiv lam ((ModuleCat.extendScalars φ).mapHomotopyEquiv h)

/-- Mapping-cone additivity assuming finite homology evaluations. -/
lemma chiLam_cone_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤)
    (P Q : PerfSupp T (algebraMap A T ∘ z)) (f : P.1 ⟶ Q.1)
    (hc : IsPerfectSupported (algebraMap A T ∘ z) (CochainComplex.mappingCone f)) :
    chiLam lam (algebraMap T C) (CochainComplex.mappingCone f) =
      chiLam lam (algebraMap T C) Q.1 - chiLam lam (algebraMap T C) P.1 := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap T C)
  let fC := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  let k : baseChange (algebraMap T C) (CochainComplex.mappingCone f) ≅ Cone.cone fC :=
    HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f F
  have hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone fC).X i) := by
    obtain ⟨a, b, hab⟩ := baseChange_bounded (algebraMap T C) _ hc.bounded
    exact ⟨a, b, fun i hi ↦ (HomologicalComplex.Hom.isoApp k i).isZero_iff.mp (hab i hi)⟩
  have tC : ∀ i, IsPowTorsion ((maximalIdeal A).map (algebraMap A C))
      ((Cone.cone fC).homology i) := fun i ↦
    IsPowTorsion.of_equiv
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso k).toLinearEquiv)
      (chiLam_homology_isPowTorsion hz hc i)
  have lC : ∀ i, lam.len ((Cone.cone fC).homology i) ≠ ⊤ := by
    intro i
    have hi := lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso k).toLinearEquiv)
    exact ne_of_eq_of_ne hi.symm (hfinite ⟨_, hc⟩ i)
  change lambdaEuler lam (baseChange (algebraMap T C) (CochainComplex.mappingCone f)) =
    lambdaEuler lam (baseChange (algebraMap T C) Q.1) -
      lambdaEuler lam (baseChange (algebraMap T C) P.1)
  rw [lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso k)]
  exact lambdaEuler_cone lam fC
    (baseChange_bounded (algebraMap T C) _ Q.2.bounded) hbound
    (chiLam_homology_isPowTorsion hz P.2) (chiLam_homology_isPowTorsion hz Q.2) tC
    (hfinite P) (hfinite Q) lC

/-- Finite evaluations let the normalized Euler evaluation descend to `K₀`. -/
noncomputable def chiLamHom_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) :
    K0Supported T (algebraMap A T ∘ z) →+ ℝ :=
  K0.lift (fun P ↦ chiLam lam (algebraMap T C) P.1)
    (fun _ _ h ↦ chiLam_eq_of_homotopyEquiv (algebraMap T C) h)
    (chiLam_cone_of_finite hz hfinite)

@[simp]
lemma chiLamHom_of_finite_mk
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤)
    (P : PerfSupp T (algebraMap A T ∘ z)) :
    chiLamHom_of_finite hz hfinite (K0.mk P) = chiLam lam (algebraMap T C) P.1 :=
  K0.lift_mk _ _ _ _

end supported

end SerrePositivity
