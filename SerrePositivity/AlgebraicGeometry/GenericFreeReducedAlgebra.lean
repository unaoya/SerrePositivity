module

public import SerrePositivity.AlgebraicGeometry.GenericFreeAlgebra
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
概要：非自明な被約 Noether 環上の有限型代数に対する、一つの主開上の一般自由性。
方針：一つの最小素イデアルを残す主開を取り、整域上の一般自由性を適用する。
規約：得られる主開は非空。基底の全成分を含む稠密開はここでは要求しない。
使われ方：Stacks 05FS の Noether 帰納で用いる自由な局所化。
-/

@[expose] public noncomputable section
universe u v w z

namespace SerrePositivity.AlgebraicGeometry
open scoped BigOperators TensorProduct

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/--
概要：係数代数の同型は、テンソル基底変更の間に係数環を移す半線形同型を誘導する。
方針：テンソル積の代数同型のスカラー作用を、左因子による積で比較する。
規約：半線形性は同型による係数環の変更について取る。
使われ方：主局所化のモデル変更と、Noether 帰納で用いる商環の同一視。
-/
def tensorBaseChangeSemilinearEquiv
    {R : Type u} {A : Type v} {C : Type w} {B : Type z}
    [CommRing R] [CommRing A] [CommRing C] [CommRing B]
    [Algebra R A] [Algebra R C] [Algebra R B] (e : A ≃ₐ[R] C) :
    (A ⊗[R] B) ≃ₛₗ[RingHomClass.toRingHom e.toRingEquiv] (C ⊗[R] B) := by
  let E := Algebra.TensorProduct.congr e (AlgEquiv.refl : B ≃ₐ[R] B)
  refine { E.toRingEquiv.toAddEquiv with map_smul' := fun a x => ?_ }
  change E (a • x) = e a • E x
  simp only [Algebra.smul_def, map_mul]
  congr 1

private theorem exists_nonzero_away_isDomain
    (R : Type u) [CommRing R] [Nontrivial R] [IsReduced R] [IsNoetherianRing R] :
    ∃ f : R, f ≠ 0 ∧ IsDomain (Localization.Away f) := by
  classical
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes (bot_ne_top : (⊥ : Ideal R) ≠ ⊤)
  let : P.IsPrime := hP.isPrime
  let finitePrimes := minimalPrimes.finite_of_isNoetherianRing (R := R)
  let others := finitePrimes.toFinset.erase P
  have hex (Q : others) : ∃ x : R, x ∈ (Q : Ideal R) ∧ x ∉ P := by
    have hQ : (Q : Ideal R) ∈ minimalPrimes R :=
      finitePrimes.mem_toFinset.mp (Finset.mem_of_mem_erase Q.property)
    by_contra! h
    have hle : (Q : Ideal R) ≤ P := fun _ hx => h _ hx
    exact (Finset.ne_of_mem_erase Q.property) (hle.antisymm (hP.2 hQ.1 hle))
  let x (Q : others) := (hex Q).choose
  let f := ∏ Q : others, x Q
  have hfP : f ∉ P := by
    intro hf
    obtain ⟨Q, _, hQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hf
    exact (hex Q).choose_spec.2 hQ
  have hfQ {Q : Ideal R} (hQ : Q ∈ minimalPrimes R) (hne : Q ≠ P) : f ∈ Q := by
    let q : others := ⟨Q, Finset.mem_erase.mpr ⟨hne, finitePrimes.mem_toFinset.mpr hQ⟩⟩
    change (∏ Q' : others, x Q') ∈ Q
    rw [← Finset.prod_erase_mul _ x (Finset.mem_univ q)]
    exact Q.mul_mem_left _ (hex q).choose_spec.1
  let C := Localization.Away f
  let Q₀ : Ideal C := P.map (algebraMap R C)
  have hdis := (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfP
  have hprime : Q₀.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) C P
    hP.isPrime hdis
  have hmin : minimalPrimes C = Ideal.under R ⁻¹' minimalPrimes R := by
    simpa only [Ideal.map_bot] using IsLocalization.minimalPrimes_map (.powers f) C (⊥ : Ideal R)
  have hQ₀ : Q₀ ∈ minimalPrimes C := by
    rw [hmin]
    change Ideal.under R Q₀ ∈ minimalPrimes R
    rwa [IsLocalization.under_map_of_isPrime_disjoint (.powers f) C hP.isPrime hdis]
  have hone : minimalPrimes C = {Q₀} := by
    ext Q
    refine ⟨fun hQ => ?_, fun he => (Set.mem_singleton_iff.mp he).symm ▸ hQ₀⟩
    have hu : Ideal.under R Q ∈ minimalPrimes R := by
      simpa only [hmin, Set.mem_preimage] using hQ
    have hunder : Ideal.under R Q = P := by
      by_contra hne
      exact hQ.isPrime.ne_top (Q.eq_top_of_isUnit_mem (hfQ hu hne)
        (IsLocalization.Away.algebraMap_isUnit (S := C) f))
    exact Set.mem_singleton_iff.mpr
      ((IsLocalization.map_under (.powers f) C Q).symm.trans
        (congrArg (Ideal.map (algebraMap R C)) hunder))
  have hzero : Q₀ = ⊥ := by
    have h := Ideal.sInf_minimalPrimes (I := (⊥ : Ideal C))
    change sInf (minimalPrimes C) = nilradical C at h
    rwa [hone, sInf_singleton, nilradical_eq_bot_iff.mpr (inferInstance : IsReduced C)] at h
  let : (⊥ : Ideal C).IsPrime := hzero ▸ hprime
  exact ⟨f, fun hf => hfP (hf ▸ P.zero_mem), IsDomain.of_bot_isPrime C⟩

/--
概要：非自明な被約 Noether 環上の有限型代数は、ある非零元を反転すると基底環上自由。
方針：整域となる主局所化で一般自由性を使い、二度の局所化を元の環の一度の局所化に戻す。
規約：自由階数の有限性は仮定しない。
使われ方：05FS の被約基底における射影性判定。
-/
theorem exists_nonzero_free_localization_of_finiteType_of_isReduced
    (R B : Type u) [CommRing R] [Nontrivial R] [IsReduced R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
    ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (Localization.Away f ⊗[R] B) := by
  obtain ⟨f, _, hdomain⟩ := exists_nonzero_away_isDomain R
  let C := Localization.Away f
  let : IsDomain C := hdomain
  obtain ⟨g, hg, hfree⟩ := exists_nonzero_free_localization_of_finiteType C (C ⊗[R] B)
  let a := (IsLocalization.Away.sec f g).1
  have ha : Associated (algebraMap R C a) g := IsLocalization.Away.associated_sec_fst f g
  let L := Localization.Away g
  let D := Localization.Away (f * a)
  have hfa : f * a ≠ 0 := by
    intro h
    have hmap := congrArg (algebraMap R C) h
    rw [map_mul, map_zero] at hmap
    exact mul_ne_zero (IsLocalization.Away.algebraMap_isUnit (S := C) f).ne_zero
      (ha.ne_zero_iff.mpr hg) hmap
  let : IsLocalization.Away (f * a) L := IsLocalization.Away.mul_of_associated f a g ha
  let e : L ≃ₐ[R] D := IsLocalization.algEquiv (.powers (f * a)) L D
  let : Module.Free L (L ⊗[C] (C ⊗[R] B)) := hfree
  let : Module.Free L (L ⊗[R] B) := Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R C L L B).toLinearEquiv
  exact ⟨f * a, hfa, Module.Free.of_equiv (tensorBaseChangeSemilinearEquiv e)⟩

end SerrePositivity.AlgebraicGeometry
