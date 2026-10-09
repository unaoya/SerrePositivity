module

public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.PerfectComplex.K0
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Ordinary Euler evaluation on supported perfect complexes

Over a Noetherian ring `T`, a perfect complex supported on the zero locus of an
ideal with Artinian quotient has finite-length homology. Its ordinary Euler
evaluation descends to the supported Grothendieck group. No normalized length
or choice of a normalization base is involved.

Homotopy invariance and mapping-cone additivity of `chiOrd` are the special case
`NormalizedLength.ordinary` of the statements in `NormalizedEuler.lean`
(`chiOrd_eq_lambdaEuler_ordinary`).
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
/-- Ordinary Euler evaluation is invariant under homotopy equivalence. -/
lemma chiOrd_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : HomotopyEquiv P Q) : chiOrd P = chiOrd Q := by
  rw [chiOrd_eq_lambdaEuler_ordinary, chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_eq_of_homotopyEquiv _ h

omit [IsNoetherianRing T] in
/-- The ordinary Euler evaluation is additive on a mapping-cone triangle when
the homology is bounded and has finite length. This is `lambdaEuler_cone` for
`NormalizedLength.ordinary`; the torsion hypotheses hold trivially for `J = ⊥`. -/
theorem chiOrd_cone {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (lP : ∀ i, Module.length T (P.homology i) ≠ ⊤)
    (lQ : ∀ i, Module.length T (Q.homology i) ≠ ⊤)
    (lC : ∀ i, Module.length T ((Cone.cone f).homology i) ≠ ⊤) :
    chiOrd (Cone.cone f) = chiOrd Q - chiOrd P := by
  simp only [chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_cone _ f hQ hC (fun _ ↦ IsPowTorsion.bot) (fun _ ↦ IsPowTorsion.bot)
    (fun _ ↦ IsPowTorsion.bot) (fun i ↦ ENat.toENNReal_ne_top.mpr (lP i))
    (fun i ↦ ENat.toENNReal_ne_top.mpr (lQ i)) (fun i ↦ ENat.toENNReal_ne_top.mpr (lC i))

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

end SerrePositivity
