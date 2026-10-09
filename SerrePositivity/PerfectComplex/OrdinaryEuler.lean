module

public import SerrePositivity.HomologicalAlgebra.ConeLES
public import SerrePositivity.PerfectComplex.K0
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Ordinary Euler evaluation on supported perfect complexes

Over a Noetherian ring `T`, a perfect complex supported on the zero locus of an
ideal with Artinian quotient has finite-length homology. Its ordinary Euler
evaluation descends to the supported Grothendieck group. No normalized length
or choice of a normalization base is involved.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T] [IsNoetherianRing T]

/-- An Artinian quotient remains Artinian when the defining ideal is replaced
by an ideal whose radical contains the original ideal. -/
lemma isArtinianRing_quotient_of_le_radical (I J : Ideal T)
    [IsArtinianRing (T ⧸ I)] (hIJ : I ≤ J.radical) : IsArtinianRing (T ⧸ J) := by
  have : IsNoetherianRing (T ⧸ J) :=
    isNoetherianRing_of_surjective T _ (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_krullDimLE_zero).mpr
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro p hp
  have : p.IsPrime := hp.1.1
  have hIp : I ≤ p := hIJ.trans ((Ideal.IsPrime.radical_le_iff ‹p.IsPrime›).mpr hp.1.2)
  have : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  have : (p.map (Ideal.Quotient.mk I)).IsMaximal := Ideal.IsPrime.isMaximal' inferInstance
  have h := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (K := p.map (Ideal.Quotient.mk I))
  simpa [Ideal.comap_map_of_surjective, sup_eq_right.mpr hIp] using h

/-- A finite module supported on an Artinian closed subscheme has finite length. -/
lemma isFiniteLength_of_le_radical_annihilator (I : Ideal T)
    [IsArtinianRing (T ⧸ I)] (M : Type u) [AddCommGroup M] [Module T M]
    [Module.Finite T M] (hI : I ≤ (Module.annihilator T M).radical) : IsFiniteLength T M := by
  have : IsArtinianRing (T ⧸ Module.annihilator T M) :=
    isArtinianRing_quotient_of_le_radical I _ hI
  let hM := Module.isTorsionBySet_annihilator T M
  let := hM.module
  let : RingHomSurjective (Ideal.Quotient.mk (Module.annihilator T M)) :=
    ⟨Ideal.Quotient.mk_surjective⟩
  have : IsNoetherian (T ⧸ Module.annihilator T M) M :=
    isNoetherian_of_surjective hM.semilinearMap
      (LinearMap.range_eq_top.mpr Function.surjective_id)
  have : IsArtinian (T ⧸ Module.annihilator T M) M := inferInstance
  have : IsArtinian T M :=
    (hM.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).mpr inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- Homology of a complex of finite modules over a Noetherian ring is finite. -/
lemma homology_moduleFinite (P : CochainComplex (ModuleCat.{u} T) ℤ) (i : ℤ)
    [Module.Finite T (P.X i)] : Module.Finite T (P.homology i) := by
  let S := P.sc i
  have : Module.Finite T S.X₂ := inferInstanceAs (Module.Finite T (P.X i))
  have : Module.Finite T S.moduleCatLeftHomologyData.H := by
    change Module.Finite T (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

omit [IsNoetherianRing T] in
/-- Null-homotopic powers of the support generators annihilate homology. -/
lemma IsSupported.le_radical_annihilator {e : ℕ} {w : Fin e → T}
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (hP : IsSupported w P) (i : ℤ) :
    Ideal.span (Set.range w) ≤ (Module.annihilator T (P.homology i)).radical := by
  obtain ⟨v, hv⟩ := hP
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  refine ⟨v, ?_⟩
  obtain ⟨H⟩ := hv j
  have h := H.homologyMap_eq i
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  rw [Module.mem_annihilator]
  intro x
  exact congrArg (fun f : P.homology i ⟶ P.homology i ↦ f.hom x) h

/-- Supported perfect complexes have finite-length homology whenever the
quotient by the support ideal is Artinian. -/
theorem homology_finiteLength_of_isPerfectSupported {e : ℕ} {w : Fin e → T}
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))]
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (hP : IsPerfectSupported w P) (i : ℤ) :
    IsFiniteLength T (P.homology i) := by
  have := hP.finite i
  have := homology_moduleFinite P i
  exact isFiniteLength_of_le_radical_annihilator _ _ (hP.supported.le_radical_annihilator i)

omit [IsNoetherianRing T] in
/-- The real-valued length of the middle term of an exact pair is the sum of
the lengths of the two images, provided the middle term has finite length. -/
lemma lengthReal_eq_add_range {M N L : Type u} [AddCommGroup M] [Module T M]
    [AddCommGroup N] [Module T N] [AddCommGroup L] [Module T L]
    (f : M →ₗ[T] N) (g : N →ₗ[T] L) (hfg : Function.Exact f g)
    (hN : Module.length T N ≠ ⊤) :
    ((Module.length T N).toNat : ℝ) = ((Module.length T (LinearMap.range f)).toNat : ℝ) +
      ((Module.length T (LinearMap.range g)).toNat : ℝ) := by
  have hk : Module.length T (LinearMap.ker g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (Module.length_le_of_injective _ (Submodule.subtype_injective _))
  have hr : Module.length T (LinearMap.range g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (Module.length_le_of_surjective _ g.surjective_rangeRestrict)
  have hlen := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict
    (by rw [LinearMap.exact_iff]; simp)
  rw [hlen, ENat.toNat_add hk hr, Nat.cast_add, ← LinearMap.exact_iff.mp hfg]

omit [IsNoetherianRing T] in
/-- Bounded complexes have finite support for the lengths of their homology. -/
lemma homologyLength_hasFiniteSupport (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    Function.HasFiniteSupport (fun i ↦ ((Module.length T (P.homology i)).toNat : ℝ)) := by
  obtain ⟨a, b, hab⟩ := hP
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hn
  have hzero : IsZero (P.homology i) :=
    (P.sc i).isZero_homology_of_isZero_X₂ (hab i (by simp only [Set.mem_Icc] at hn; omega))
  have := ModuleCat.subsingleton_of_isZero hzero
  exact hi (by simp [Module.length_eq_zero])

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

omit [IsNoetherianRing T] in
/-- Ordinary Euler evaluation is invariant under homotopy equivalence. -/
lemma chiOrd_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : HomotopyEquiv P Q) : chiOrd P = chiOrd Q := by
  unfold chiOrd
  congr 1
  funext i
  rw [(h.toHomologyIso i).toLinearEquiv.length_eq]

set_option maxHeartbeats 800000 in
-- Transporting the three exact sequences with dependent homology objects
-- requires additional elaboration time.
omit [IsNoetherianRing T] in
/-- The ordinary Euler evaluation is additive on a mapping-cone triangle when
the homology is bounded and has finite length. -/
theorem chiOrd_cone {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (lP : ∀ i, Module.length T (P.homology i) ≠ ⊤)
    (lQ : ∀ i, Module.length T (Q.homology i) ≠ ⊤)
    (lC : ∀ i, Module.length T ((Cone.cone f).homology i) ≠ ⊤) :
    chiOrd (Cone.cone f) = chiOrd Q - chiOrd P := by
  let α := fun i ↦ (HomologicalComplex.homologyMap f i).hom
  let β := fun i ↦ (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i).hom
  let δ := fun i ↦ (Cone.δ f i (i + 1) rfl).hom
  let a := fun i ↦ ((Module.length T (LinearMap.range (α i))).toNat : ℝ)
  let b := fun i ↦ ((Module.length T (LinearMap.range (β i))).toNat : ℝ)
  let d := fun i ↦ ((Module.length T (LinearMap.range (δ i))).toNat : ℝ)
  have ha : Function.HasFiniteSupport a := by
    apply (homologyLength_hasFiniteSupport Q hQ).subset
    intro i hi hz
    have hz' : Module.length T (Q.homology i) = 0 := by
      have hn := lQ i
      simpa [hn] using hz
    have : Module.length T (LinearMap.range (α i)) = 0 :=
      le_antisymm (hz' ▸ Module.length_le_of_injective _ (Submodule.subtype_injective _)) bot_le
    exact hi (by simp [a, this])
  have hb : Function.HasFiniteSupport b := by
    apply (homologyLength_hasFiniteSupport (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : Module.length T ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [hn] using hz
    have : Module.length T (LinearMap.range (β i)) = 0 :=
      le_antisymm (hz' ▸ Module.length_le_of_injective _ (Submodule.subtype_injective _)) bot_le
    exact hi (by simp [b, this])
  have hd : Function.HasFiniteSupport d := by
    apply (homologyLength_hasFiniteSupport (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : Module.length T ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [hn] using hz
    have : Module.length T (LinearMap.range (δ i)) = 0 :=
      le_antisymm (hz' ▸ Module.length_le_of_surjective _ (δ i).surjective_rangeRestrict) bot_le
    exact hi (by simp [d, this])
  have hQlen : ∀ i, ((Module.length T (Q.homology i)).toNat : ℝ) = a i + b i := fun i ↦
    lengthReal_eq_add_range (α i) (β i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (Cone.exact₂ f i)) (lQ i)
  have hClen : ∀ i, ((Module.length T ((Cone.cone f).homology i)).toNat : ℝ) = b i + d i := fun i ↦
    lengthReal_eq_add_range (β i) (δ i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₃ f i (i + 1) rfl)) (lC i)
  have hPlen : ∀ i, ((Module.length T (P.homology i)).toNat : ℝ) = d (i - 1) + a i := by
    intro i
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact lengthReal_eq_add_range (δ j) (α (j + 1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₁ f j (j + 1) rfl)) (lP (j + 1))
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
  have eQ : chiOrd Q = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) := by
    simp_rw [chiOrd, hQlen, mul_add]
    exact finsum_add_distrib haw hbw
  have eC : chiOrd (Cone.cone f) = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) := by
    simp_rw [chiOrd, hClen, mul_add]
    exact finsum_add_distrib hbw hdw
  have eP : chiOrd P = -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) := by
    simp_rw [chiOrd, hPlen, mul_add]
    rw [finsum_add_distrib hds haw, alternating_finsum_shift]
  rw [eC, eQ, eP]
  ring

/-- Ordinary Euler evaluation as a homomorphism on the supported Grothendieck
group over a Noetherian ring with Artinian support quotient. -/
noncomputable def chiOrdHom {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] : K0Supported T w →+ ℝ :=
  K0.lift (fun P ↦ chiOrd P.1)
    (fun _ _ h ↦ chiOrd_eq_of_homotopyEquiv h)
    (fun P Q f hc ↦ chiOrd_cone f Q.2.bounded hc.bounded
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported P.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported Q.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported hc i)))

@[simp]
lemma chiOrdHom_mk {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] (P : PerfSupp T w) :
    chiOrdHom w (K0.mk P) = chiOrd P.1 := K0.lift_mk _ _ _ _

/-- The finite-length and homomorphism assertions for ordinary Euler evaluation,
in a setting independent of the paper's normalization base. -/
theorem ordinary_euler_of_artinian_quotient {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] :
    (∀ (P : PerfSupp T w) (i : ℤ), Module.length T (P.1.homology i) ≠ ⊤) ∧
      (∃ χ : K0Supported T w →+ ℝ, ∀ P, χ (K0.mk P) = chiOrd P.1) :=
  ⟨fun P i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported P.2 i),
    chiOrdHom w, chiOrdHom_mk w⟩

end SerrePositivity
