module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.StratumQuotient
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.StratumLocalization
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.StratumBaseChange
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.StratumEquiv
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericLocalization
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericSpread
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericRadicial
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.ReducedSpread
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Int.NatPrime
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericPoints
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericBijective
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericModel
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.ReducedEtale
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericNil
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.NoetherianInduction
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericFactorization

/-!
# 有限表示有限射の有限エタール層別（BS 著者版 Lemma 10.12）

## 概要
R → S を可換 Z_(p) 代数の有限表示有限射とする。g_1,…,g_n ∈ R があって、
R_i := R/(g_1,…,g_{i−1})_red[1/g_i]、S_i := S/(g_1,…,g_{i−1})_red[1/g_i] と置くと
(1) (g_1,…,g_n) = R、(2) R_i → S_i は R_i → T_i → S_i と分解し
R_i → T_i は有限エタール、T_i → S_i は普遍同相（さらに T_i[1/p] → S_i[1/p] は同型）、
(3) 各 R_i で p = 0 または p ∈ R_i^×。

## 方針
原典の証明：表示の係数で有限生成 Z_(p) 部分代数 R_0 に近似（noetherian）、極小素イデアルの剰余体の積 K 上で S_0 ⊗ K の被約化は有限体拡大の積、
各拡大は分離閉包（有限エタール）と純非分離（普遍同相）に分解、全商環から主開集合 D(g_1) に広げ、noetherian 帰納。(3) は (pg_i, g_i) で細分。

## 規約
普遍同相は「整・Spec 全射・radicial」で定義（G-A8-4）。剰余体の代数構造は各点の標準射から取る。

## 使われ方
BS 著者版 Theorem 10.11（A8-4）。
-/

@[expose] public section
noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- ℤ_(p) の表示と、p 以外の素数が可逆な環への構造射。 -/
abbrev strataPrimeIdeal (p : ℕ) := Ideal.span {(p : ℤ)}

instance strataPrimeIdeal_isPrime (p : ℕ) [hp : Fact p.Prime] : (strataPrimeIdeal p).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp hp.out)

abbrev StrataBase (p : ℕ) [Fact p.Prime] := Localization.AtPrime (strataPrimeIdeal p)

def strataBaseMap (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : StrataBase p →+* R :=
  IsLocalization.lift (M := (strataPrimeIdeal p).primeCompl) (g := Int.castRingHom R)
    (by
      have units : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : R) := by
        apply induction_on_primes
        · simp
        · simp
        · intro q n hq ih h
          have hqp : q ≠ p := by
            rintro rfl
            exact h (dvd_mul_right _ _)
          simpa using (hZp q hq hqp).mul (ih fun hn ↦ h (dvd_mul_of_dvd_right hn q))
      intro z
      have hz : ¬ (p : ℤ) ∣ (z : ℤ) := fun h ↦ z.property (Ideal.mem_span_singleton.mpr h)
      have hu := units (z : ℤ).natAbs (fun h ↦ hz (Int.natCast_dvd.mpr h))
      rcases Int.natAbs_eq (z : ℤ) with he | he
      · change IsUnit ((z : ℤ) : R)
        rw [he, Int.cast_natCast]
        exact hu
      · change IsUnit ((z : ℤ) : R)
        rw [he, Int.cast_neg, Int.cast_natCast]
        exact hu.neg)

/-- 指定した有限個の係数を含む有限生成 noetherian 部分代数。
近似に必要な関係式・モニック関係の係数を加えた有限集合にも適用する。 -/
theorem exists_fg_noetherian_subalgebra_containing (p : ℕ) [Fact p.Prime]
    (R : Type u) [CommRing R]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (coeffs : Finset R) :
    letI := (strataBaseMap p R hZp).toAlgebra
    ∃ R₀ : Subalgebra (StrataBase p) R,
      (∀ c ∈ coeffs, c ∈ R₀) ∧ R₀.FG ∧ IsNoetherianRing R₀ := by
  let := (strataBaseMap p R hZp).toAlgebra
  let R₀ := Algebra.adjoin (StrataBase p) (coeffs : Set R)
  have hfg : R₀.FG := Subalgebra.fg_adjoin_finset coeffs
  refine ⟨R₀, fun c hc ↦ Algebra.subset_adjoin hc, hfg, ?_⟩
  exact isNoetherianRing_of_fg hfg

/-- モニック関係の係数が小さい部分代数に属すれば、その部分代数上でも整。 -/
theorem isIntegral_of_monic_coeffs_mem {C R S : Type*}
    [CommRing C] [CommRing R] [CommRing S] [Algebra C R] [Algebra R S]
    (R₀ : Subalgebra C R) (x : S) (f : Polynomial R) (hf : f.Monic)
    (hx : Polynomial.aeval x f = 0) (hc : (f.coeffs : Set R) ⊆ R₀) : IsIntegral R₀ x := by
  have hlift : f ∈ Polynomial.lifts (algebraMap R₀ R) :=
    (Polynomial.lifts_iff_coeffs_subset_range f).mpr fun c h ↦ ⟨⟨c, hc h⟩, rfl⟩
  obtain ⟨g, hg⟩ := (Polynomial.mem_lifts f).mp hlift
  refine ⟨g, Polynomial.monic_of_injective (FaithfulSMul.algebraMap_injective R₀ R)
    (by rw [hg]; exact hf), ?_⟩
  change Polynomial.aeval x g = 0
  rw [← Polynomial.aeval_map_algebraMap R x g, hg]
  exact hx

/-- 有限個の整な生成元のモニック関係に必要な係数を、一つの有限集合にまとめる。 -/
theorem exists_integrality_coefficients {C R S : Type*}
    [CommRing C] [CommRing R] [CommRing S] [Algebra C R] [Algebra R S]
    {ι : Type*} [Finite ι] (v : ι → S) (hv : ∀ i, IsIntegral R (v i)) :
    ∃ coeffs : Finset R, ∀ R₀ : Subalgebra C R,
      (∀ c ∈ coeffs, c ∈ R₀) → ∀ i, IsIntegral R₀ (v i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose f hf hx using hv
  refine ⟨Finset.univ.biUnion fun i ↦ (f i).coeffs, ?_⟩
  intro R₀ hc i
  apply isIntegral_of_monic_coeffs_mem R₀ (v i) (f i) (hf i) (hx i)
  intro c h
  exact hc c (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)

/-- 表示の係数を含む部分環上で、生成元の像の部分代数を底変換すると元の代数に戻る。 -/
private theorem presentation_range_baseChange_equiv {C R S : Type*}
    [CommRing C] [CommRing R] [CommRing S] [Algebra C R] [Algebra R S]
    {ι σ : Type*} (P : Algebra.Presentation R S ι σ) (R₀ : Subalgebra C R)
    [P.HasCoeffs R₀] :
    Nonempty ((R ⊗[R₀] (MvPolynomial.aeval (R := R₀) P.val).range) ≃ₐ[R] S) := by
  let e := MvPolynomial.aeval (R := R₀) P.val
  let S₀ := e.range
  let q : P.ModelOfHasCoeffs R₀ →ₐ[R₀] S₀ :=
    Ideal.Quotient.liftₐ _ e.rangeRestrict (by
      change Ideal.span (Set.range (P.relationOfHasCoeffs R₀)) ≤
        RingHom.ker e.rangeRestrict
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      apply Subtype.ext
      exact P.aeval_val_relationOfHasCoeffs R₀ i)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨t, ht⟩ := e.rangeRestrict_surjective x
    exact ⟨Ideal.Quotient.mk _ t, ht⟩
  let u : R ⊗[R₀] P.ModelOfHasCoeffs R₀ →ₐ[R] R ⊗[R₀] S₀ :=
    Algebra.TensorProduct.map (AlgHom.id R R) q
  let v : R ⊗[R₀] S₀ →ₐ[R] S :=
    Algebra.TensorProduct.lift (Algebra.ofId R S) S₀.val fun _ _ ↦ Commute.all _ _
  have hu : Function.Surjective u :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hq
  have he : v.comp u = (P.tensorModelOfHasCoeffsEquiv R₀).toAlgHom := by
    ext x
    induction x using Quotient.inductionOn' with
    | h t =>
      change v (u ((1 : R) ⊗ₜ[R₀] (Ideal.Quotient.mk _ t))) =
        P.tensorModelOfHasCoeffsEquiv R₀ ((1 : R) ⊗ₜ[R₀] (Ideal.Quotient.mk _ t))
      rw [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul]
      simp [u, v, q, e, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
  have hbij : Function.Bijective (v.comp u) := by
    rw [he]
    exact (P.tensorModelOfHasCoeffsEquiv R₀).bijective
  have hv : Function.Surjective v := by
    intro y
    obtain ⟨x, hx⟩ := hbij.surjective y
    exact ⟨u x, hx⟩
  refine ⟨AlgEquiv.ofBijective v ⟨?_, hv⟩⟩
  intro x y hxy
  obtain ⟨x, rfl⟩ := hu x
  obtain ⟨y, rfl⟩ := hu y
  exact congrArg u (hbij.injective hxy)

/-- 概要：noetherian 近似：有限表示有限 R → S は、有限生成 Z_(p) 部分代数 R_0 ⊂ R と有限表示有限 R_0 → S_0 の底変換。
方針：表示 S = R[x]/(h_1..h_m)（モニック関係を含む）の係数で R_0 を生成。
規約：—
使われ方：noetherian の場合に帰着。 -/
theorem exists_noetherianApproximation {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] (p : ℕ) [Fact p.Prime]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (coeffs : Finset R) :
    letI := (strataBaseMap p R hZp).toAlgebra
    ∃ (R₀ : Subalgebra (StrataBase p) R) (S₀ : CommRingCat.{u}) (a₀ : Algebra R₀ S₀),
      letI : Algebra R₀ S₀ := a₀
      letI : Algebra R (S₀ ⊗[R₀] R) :=
        (Algebra.TensorProduct.includeRight : R →ₐ[R₀] S₀ ⊗[R₀] R).toRingHom.toAlgebra
      (∀ c ∈ coeffs, c ∈ R₀) ∧ R₀.FG ∧ IsNoetherianRing R₀ ∧ Module.Finite R₀ S₀ ∧
        Algebra.FinitePresentation R₀ S₀ ∧ Nonempty ((S₀ ⊗[R₀] R) ≃ₐ[R] S) := by
  classical
  let : Algebra (StrataBase p) R := (strataBaseMap p R hZp).toAlgebra
  let P := Algebra.Presentation.ofFinitePresentation R S
  obtain ⟨ci, hi⟩ := exists_integrality_coefficients (C := StrataBase p) P.val
    (fun i ↦ Algebra.IsIntegral.isIntegral (R := R) (P.val i))
  let cr := P.finite_coeffs.toFinset
  obtain ⟨R₀, hc, hfg, hn⟩ := exists_fg_noetherian_subalgebra_containing p R hZp
    (coeffs ∪ ci ∪ cr)
  let : IsNoetherianRing R₀ := hn
  have hci (c : R) (h : c ∈ ci) : c ∈ R₀ := hc c (by simp [h])
  let : P.HasCoeffs R₀ := ⟨fun c h ↦ ⟨⟨c, hc c (by simp [cr, h])⟩, rfl⟩⟩
  let e := MvPolynomial.aeval (R := R₀) P.val
  let S₀ := e.range
  have hint : ∀ x ∈ Set.range P.val, IsIntegral R₀ x := by
    rintro _ ⟨i, rfl⟩
    exact hi R₀ hci i
  have hfinite : Module.Finite R₀ S₀ := by
    let : Module.Finite R₀ (Algebra.adjoin R₀ (Set.range P.val)) :=
      Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range P.val) hint
    have he : Algebra.adjoin R₀ (Set.range P.val) = S₀ :=
      (MvPolynomial.aeval_range (R := R₀) P.val).symm
    exact Module.Finite.equiv (Subalgebra.equivOfEq _ _ he).toLinearEquiv
  let : Module.Finite R₀ S₀ := hfinite
  have hfp : Algebra.FinitePresentation R₀ S₀ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨hiso⟩ := presentation_range_baseChange_equiv P R₀
  refine ⟨R₀, CommRingCat.of S₀, inferInstance, ?_, hfg, hn, hfinite, hfp, ?_⟩
  · intro c h
    exact hc c (by simp [h])
  · let : Algebra R (S₀ ⊗[R₀] R) := Algebra.TensorProduct.rightAlgebra
    exact ⟨(Algebra.TensorProduct.commRight R₀ R S₀).symm.trans hiso⟩

/-- 概要：全商環での分解を或る D(g_1) に広げる：
R_0,red[1/g_1] → T_1 有限エタール、T_1 → S_0,red[1/g_1] 普遍同相。
方針：有限個の等式を分母を払って広げる。 -/
theorem spread_out_generic (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃ g : R, (∀ P : GenericPoint R, g ∉ P.val.asIdeal) ∧
      HasEtaleFactorization p (stratumMap (algebraMap R S) ⊥ g) := by
  let I : Ideal R := (⊥ : Ideal R).radical
  let J : Ideal S := ((⊥ : Ideal R).map (algebraMap R S)).radical
  let R₀ := R ⧸ I
  let S₀ := S ⧸ J
  let q : R₀ →+* S₀ := Ideal.quotientMap J (algebraMap R S)
    (Ideal.map_le_iff_le_comap.mp (Ideal.map_radical_le (algebraMap R S)))
  let : Algebra R₀ S₀ := q.toAlgebra
  let : IsScalarTower R R₀ S₀ := IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  let : IsReduced R₀ := (Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_isRadical _)
  let : IsReduced S₀ := (Ideal.isRadical_iff_quotient_reduced J).mp (Ideal.radical_isRadical _)
  let : Module.Finite R S₀ := Module.Finite.trans S S₀
  let : Module.Finite R₀ S₀ := Module.Finite.of_restrictScalars_finite R R₀ S₀
  have hZp₀ : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R₀) := by
    intro q hq hqp
    simpa only [map_natCast] using (hZp q hq hqp).map (Ideal.Quotient.mk I)
  obtain ⟨g₀, hfac⟩ := exists_reduced_spread_out R₀ S₀ p hZp₀
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (g₀ : R₀)
  refine ⟨g, ?_, ?_⟩
  · intro P hP
    have hmin : P.val.asIdeal ∈ I.minimalPrimes := by
      dsimp only [I]
      rw [Ideal.radical_minimalPrimes]
      exact P.property
    rw [Ideal.minimalPrimes_eq_comap] at hmin
    obtain ⟨Q, hQ, hQP⟩ := hmin
    have hmem : (g₀ : R₀) ∈ Q := by
      rw [← hg]
      change g ∈ Ideal.comap (Ideal.Quotient.mk I) Q
      rwa [hQP]
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hQ g₀.property
  · have hf : HasEtaleFactorization p (Localization.awayMap q (Ideal.Quotient.mk I g)) := by
      change HasEtaleFactorization p (Localization.awayMap q (g₀ : R₀)) at hfac
      rw [hg]
      exact hfac
    have he : stratumMap (algebraMap R S) ⊥ g =
        Localization.awayMap q (Ideal.Quotient.mk I g) := by
      apply stratumRing_hom_ext ⊥ g
      intro x
      rw [stratumMap_unit]
      change algebraMap S₀ (Localization.Away (q (Ideal.Quotient.mk I g)))
          (q (Ideal.Quotient.mk I x)) =
        Localization.awayMap q (Ideal.Quotient.mk I g)
          (algebraMap R₀ (Localization.Away (Ideal.Quotient.mk I g)) (Ideal.Quotient.mk I x))
      symm
      unfold Localization.awayMap IsLocalization.Away.map
      exact IsLocalization.map_eq _ _
    rw [he]
    exact hf

/-- 真の閉集合上に、空でない分解層を一つ選ぶ。 -/
theorem exists_factorization_stratum_not_mem
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ g : R, g ∉ I ∧ HasEtaleFactorization p (stratumMap (algebraMap R S) I g) := by
  let R₀ := R ⧸ I
  let J := I.map (algebraMap R S)
  let S₀ := S ⧸ J
  let q := quotientStratumBaseMap (algebraMap R S) I
  let : Algebra R₀ S₀ := q.toAlgebra
  let : IsScalarTower R R₀ S₀ := IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  let : Nontrivial R₀ := Ideal.Quotient.nontrivial_iff.mpr hI
  let : Module.Finite R S₀ := Module.Finite.trans S S₀
  let : Module.Finite R₀ S₀ := Module.Finite.of_restrictScalars_finite R R₀ S₀
  let : Algebra.FinitePresentation R₀ S₀ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hZp₀ : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R₀) := by
    intro q hq hqp
    simpa only [map_natCast] using (hZp q hq hqp).map (Ideal.Quotient.mk I)
  obtain ⟨g₀, havoid, hfac⟩ := spread_out_generic R₀ S₀ p hZp₀
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective g₀
  refine ⟨g, ?_, hasEtaleFactorization_of_quotient_stratum p (algebraMap R S) I g ?_⟩
  · intro hmem
    obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes (show (⊥ : Ideal R₀) ≠ ⊤ from bot_ne_top)
    let Q' : GenericPoint R₀ := ⟨⟨Q, hQ.isPrime⟩, hQ⟩
    apply havoid Q'
    rw [← hg, Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
    exact Q.zero_mem
  · change HasEtaleFactorization p (stratumMap q ⊥ g₀) at hfac
    change HasEtaleFactorization p (stratumMap q ⊥ (Ideal.Quotient.mk I g))
    rw [hg]
    exact hfac

/-- Noetherian 基底上の有限エタール層別（BS 著者版 Lemma 10.12 の基底が Noetherian の場合）。
  各段で p 可逆な部分を先に選び、
それが空なら p = 0 の部分を選ぶ。 -/
theorem exists_noetherian_finiteEtaleStratification
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, HasEtaleFactorization p (stratumMap (algebraMap R S) (earlierIdeal g i) (g i)) ∧
        ((p : StratumRing (earlierIdeal g i) (g i)) = 0 ∨
          IsUnit (p : StratumRing (earlierIdeal g i) (g i))) := by
  let P : Ideal R → R → Prop := fun I g ↦
    HasEtaleFactorization p (stratumMap (algebraMap R S) I g) ∧
      ((p : StratumRing I g) = 0 ∨ IsUnit (p : StratumRing I g))
  have hstep (I : Ideal R) (hI : I ≠ ⊤) : ∃ g : R, g ∉ I ∧ P I g := by
    obtain ⟨g, hg, hfac⟩ := exists_factorization_stratum_not_mem R S p hZp I hI
    by_cases hpg : (p : R) * g ∈ I.radical
    · exact ⟨g, hg, hfac, Or.inl (natCast_eq_zero_stratum_of_mul_mem I g p hpg)⟩
    · refine ⟨(p : R) * g, fun h ↦ hpg (Ideal.le_radical h), ?_,
        Or.inr (isUnit_natCast_stratum_mul I g p)⟩
      have h := hasEtaleFactorization_stratum_mul p (algebraMap R S) I g (p : R) hfac
      rw [mul_comm g (p : R)] at h
      exact h
  obtain ⟨n, g, hg, hPg⟩ := exists_finite_ideal_filtration P hstep ⊥
  exact ⟨n, g, by simpa using hg, fun i ↦ by simpa [P] using hPg i⟩

/-- ℤ_(p) 上の代数では、p 以外の素数は可逆。 -/
theorem isUnit_prime_of_strataBaseAlgebra (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (StrataBase p) A]
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) : IsUnit (q : A) := by
  have hmem : (q : ℤ) ∈ (strataPrimeIdeal p).primeCompl := by
    intro h
    have hd : p ∣ q := Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp h)
    exact hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp hd).symm
  have hu : IsUnit (q : StrataBase p) := by
    simpa only [map_natCast] using
      (IsLocalization.map_units (StrataBase p) (⟨(q : ℤ), hmem⟩ : (strataPrimeIdeal p).primeCompl))
  simpa only [map_natCast] using hu.map (algebraMap (StrataBase p) A)

/-- 概要：有限表示有限射 R → S を、有限エタール射と普遍同相に分解できる層に分ける（BS 著者版 Lemma 10.12）。
方針：noetherian 近似、一般点での分解、その広げ、R_0/(g_1) への noetherian 帰納、
(pg_i, g_i) での細分（紙 5）。
規約：原典の BS 著者版 Lemma 10.12。Z_(p) の仮定を保つ（W9-III-07）。
q ≠ p、K = F_q(t) → K(t^{1/q}) は有限表示有限な純非分離拡大で、非空の層では p が可逆
なので (2) が有限エタールを要求し矛盾する。E3 の perfectoid 基底は Z_(p) 代数なので下流の一般性は失われない。
使われ方：BS 著者版 Theorem 10.11。 -/
theorem exists_finiteEtaleStratification {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] (p : ℕ) [Fact p.Prime]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i : Fin n,
        let I := earlierIdeal g i
        let Rᵢ := StratumRing I (g i)
        HasEtaleFactorization p (stratumMap (algebraMap R S) I (g i)) ∧
          ((p : Rᵢ) = 0 ∨ IsUnit (p : Rᵢ)) := by
  classical
  let : Algebra (StrataBase p) R := (strataBaseMap p R hZp).toAlgebra
  obtain ⟨R₀, S₀, a₀, _, _, hn, hfin, hfp, ⟨e⟩⟩ :=
    exists_noetherianApproximation (R := R) (S := S) p hZp ∅
  let : Algebra R₀ S₀ := a₀
  let : IsNoetherianRing R₀ := hn
  let : Module.Finite R₀ S₀ := hfin
  let : Algebra.FinitePresentation R₀ S₀ := hfp
  let : Algebra R (S₀ ⊗[R₀] R) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨n, g₀, hg₀, hstrata⟩ := exists_noetherian_finiteEtaleStratification R₀ S₀ p
    (isUnit_prime_of_strataBaseAlgebra p R₀)
  let g : Fin n → R := fun i ↦ algebraMap R₀ R (g₀ i)
  have hgen : Ideal.span (Set.range g) = ⊤ := by
    have h := congrArg (Ideal.map (algebraMap R₀ R)) hg₀
    change Ideal.span (Set.range ((algebraMap R₀ R) ∘ g₀)) = ⊤
    simpa only [Ideal.map_span, Ideal.map_top, ← Set.range_comp] using h
  refine ⟨n, g, hgen, ?_⟩
  intro i
  have hI : earlierIdeal g i = (earlierIdeal g₀ i).map (algebraMap R₀ R) := by
    simp only [earlierIdeal, Ideal.map_span, Set.image_image]
    rfl
  constructor
  · have hbase := hasEtaleFactorization_stratum_baseChange R₀ S₀ R p
      (earlierIdeal g₀ i) (g₀ i) (hstrata i).1
    apply hasEtaleFactorization_stratum_of_algEquiv p e
    rw [hI]
    exact hbase
  · let f := stratumMap (algebraMap R₀ R) (earlierIdeal g₀ i) (g₀ i)
    rw [hI]
    rcases (hstrata i).2 with hz | hu
    · left
      simpa only [map_natCast, map_zero] using congrArg f hz
    · right
      simpa only [map_natCast] using hu.map f

end SerrePositivity.CommutativeAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 10.12"] _root_.SerrePositivity.CommutativeAlgebra.exists_finiteEtaleStratification
attribute [cite BS19 "Lemma 10.12"] _root_.SerrePositivity.CommutativeAlgebra.exists_noetherian_finiteEtaleStratification
