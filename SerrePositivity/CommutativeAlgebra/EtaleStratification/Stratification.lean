module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.StratumQuotient
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Int.NatPrime
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
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
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericSeparable

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
Thm 10.11（A8-4）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 有限分離体拡大はエタール。一般点での分離部分に用いる。 -/
theorem etale_of_finite_separable (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : Algebra.Etale K L := by
  exact ⟨Algebra.FormallyEtale.of_isSeparable K L,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

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
    Algebra.TensorProduct.map_surjective Function.surjective_id hq
  have he : v.comp u = (P.tensorModelOfHasCoeffsEquiv R₀).toAlgHom := by
    ext r x
    induction x using Quotient.inductionOn' with
    | h t => rfl
  have hbij : Function.Bijective (v.comp u) := by
    rw [he]
    exact (P.tensorModelOfHasCoeffsEquiv R₀).bijective
  refine ⟨AlgEquiv.ofBijective v ⟨?_, hbij.surjective.of_comp⟩⟩
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
    (fun i ↦ Algebra.IsIntegral.isIntegral (P.val i))
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
    dsimp [S₀, e]
    rw [MvPolynomial.aeval_range]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range P.val) hint
  let : Module.Finite R₀ S₀ := hfinite
  have hfp : Algebra.FinitePresentation R₀ S₀ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨hiso⟩ := presentation_range_baseChange_equiv P R₀
  refine ⟨R₀, CommRingCat.of S₀, inferInstance, ?_, hfg, hn, hfinite, hfp, ?_⟩
  · intro c h
    exact hc c (by simp [h])
  · exact ⟨(Algebra.TensorProduct.commRight R₀ R S₀).symm.trans hiso⟩

/-- Z_(p) 環から射を持つ体で p が可逆なら、全素数が非零なので標数 0。 -/
theorem strataField_charZero_of_isUnit {R K : Type u} [CommRing R] [Field K]
    (p : ℕ) (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (f : R →+* K) (hp : IsUnit (p : K)) : CharZero K := by
  apply (CharZero.charZero_iff_forall_prime_ne_zero K).mpr
  intro q hq
  by_cases he : q = p
  · subst q
    exact hp.ne_zero
  · have hu := (hZp q hq he).map f
    rw [map_natCast] at hu
    exact hu.ne_zero

/-- 一般点の剰余体について、p 可逆な因子は標数 0。 -/
theorem genericField_charZero_of_isUnit (R : Type u) [CommRing R]
    (p : ℕ) (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (P : GenericPoint R) (hp : IsUnit (p : GenericField P)) : CharZero (GenericField P) :=
  strataField_charZero_of_isUnit p hZp (algebraMap R (GenericField P)) hp

/-- 有限体拡大の分離部分は有限エタール、残りは純非分離。
p 可逆から標数 0 が従う場合には、後半の射は全単射になる。 -/
theorem separableClosure_strata_factorization (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (p : ℕ)
    (hchar : IsUnit (p : K) → CharZero K) :
    let M := separableClosure K L
    Module.Finite K M ∧ Algebra.Etale K M ∧ IsPurelyInseparable M L ∧
      (IsUnit (p : K) → Function.Bijective (algebraMap M L)) := by
  let M := separableClosure K L
  refine ⟨inferInstance, etale_of_finite_separable K M, inferInstance, ?_⟩
  intro hp
  let : CharZero K := hchar hp
  let : CharZero M := inferInstance
  exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable M L

/-- 概要：noetherian 被約 R_0 の全商環 K = ∏ κ(𝔭_i)（極小素イデアル）上で、S_0 ⊗ K の被約化は有限体拡大の有限積 ∏ L_i、各 κ(𝔭_i) → L_i は
分離閉包 M_i を経て κ → M_i 有限エタール、M_i → L_i 純非分離。
方針：Mathlib `minimalPrimes`（有限）、有限被約 K 代数＝体の積、`separableClosure`。 -/
theorem generic_structure (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsReduced R] [Module.Finite R S] (p : ℕ) [Fact p.Prime]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    letI : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
    letI : Module R (GenericProduct R) := Algebra.toModule
    Finite (GenericPoint R) ∧ IsLocalization (nonZeroDivisors R) (GenericProduct R) ∧
      (∀ P : GenericPoint R, IsUnit (p : GenericField P) → CharZero (GenericField P)) ∧
      ∃ (m : ℕ) (v : Fin m → GenericPoint R) (L : Fin m → Type u) (hL : ∀ j, Field (L j)),
        letI : ∀ j, Field (L j) := hL
        ∃ a : ∀ j, Algebra (GenericField (v j)) (L j),
          letI : ∀ j, Algebra (GenericField (v j)) (L j) := a
          letI : Algebra (GenericProduct R) (∀ j, L j) := (RingHom.pi (fun j =>
            (algebraMap (GenericField (v j)) (L j)).comp
              (Pi.evalRingHom GenericField (v j)))).toAlgebra
          Nonempty (((GenericProduct R ⊗[R] S) ⧸ nilradical (GenericProduct R ⊗[R] S))
            ≃ₐ[GenericProduct R] (∀ j, L j)) ∧
            ∀ j,
              let k := GenericField (v j)
              let M := separableClosure k (L j)
              FiniteDimensional k (L j) ∧ Module.Finite k M ∧ Algebra.Etale k M ∧
                IsPurelyInseparable M (L j) ∧
                (IsUnit (p : k) → Function.Bijective (algebraMap M (L j))) := by
  let : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
  let : Module R (GenericProduct R) := Algebra.toModule
  have hdecomp : IsLocalization (nonZeroDivisors R) (GenericProduct R) ∧
      ∃ (m : ℕ) (v : Fin m → GenericPoint R) (L : Fin m → Type u) (hL : ∀ j, Field (L j)),
        letI : ∀ j, Field (L j) := hL
        ∃ a : ∀ j, Algebra (GenericField (v j)) (L j),
          letI : ∀ j, Algebra (GenericField (v j)) (L j) := a
          letI : Algebra (GenericProduct R) (∀ j, L j) := (RingHom.pi (fun j =>
            (algebraMap (GenericField (v j)) (L j)).comp
              (Pi.evalRingHom GenericField (v j)))).toAlgebra
          Nonempty (((GenericProduct R ⊗[R] S) ⧸ nilradical (GenericProduct R ⊗[R] S))
            ≃ₐ[GenericProduct R] (∀ j, L j)) ∧
            ∀ j, FiniteDimensional (GenericField (v j)) (L j) := by
    let : Finite (GenericPoint R) := finite_genericPoint R
    exact ⟨isLocalization_genericProduct R,
      finite_algebra_over_field_product GenericField (GenericProduct R ⊗[R] S)⟩
  obtain ⟨hloc, m, v, L, hL, a, he, hfinite⟩ := hdecomp
  let : ∀ j, Field (L j) := hL
  let : ∀ j, Algebra (GenericField (v j)) (L j) := a
  refine ⟨finite_genericPoint R, hloc,
    fun P hp ↦ genericField_charZero_of_isUnit R p hZp P hp,
    m, v, L, hL, a, he, ?_⟩
  intro j
  let : FiniteDimensional (GenericField (v j)) (L j) := hfinite j
  exact ⟨hfinite j, separableClosure_strata_factorization
    (GenericField (v j)) (L j) p (genericField_charZero_of_isUnit R p hZp (v j))⟩

/-- 概要：全商環での分解を或る D(g_1) に広げる：
R_0,red[1/g_1] → T_1 有限エタール、T_1 → S_0,red[1/g_1] 普遍同相。
方針：有限個の等式を分母を払って広げる。 -/
theorem spread_out_generic (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃ g : R, (∀ P : GenericPoint R, g ∉ P.val.asIdeal) ∧
      HasEtaleFactorization p (stratumMap (algebraMap R S) ⊥ g) := by
  sorry -- 被約基底の generic_structure の冪等元・生成元・関係の分母を同時に払い、全極小点を残す。
        -- エタール locus の開性、標数 p の判定、標数 0 の逆射も広げて p 反転後の同型を得る

/-- 概要：Lemma 10.12（原典の形）：有限表示有限 R → S（R は **Z_(p) 代数**：p 以外の素数は R で可逆）に層別 g_1,…,g_n：(1)(2)(3)。
方針：noetherian 近似、一般点での分解、その広げ、R_0/(g_1) への noetherian 帰納、
(pg_i, g_i) での細分（紙 5）。
規約：原典の Lemma 10.12。Z_(p) の仮定を保つ（W9-III-07）。
q ≠ p、K = F_q(t) → K(t^{1/q}) は有限表示有限な純非分離拡大で、非空の層では p が可逆
なので (2) が有限エタールを要求し矛盾する。E3 の perfectoid 基底は Z_(p) 代数なので下流の一般性は失われない。
使われ方：Thm 10.11。 -/
theorem exists_finiteEtaleStratification {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] (p : ℕ) [Fact p.Prime]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i : Fin n,
        let I := earlierIdeal g i
        let Rᵢ := StratumRing I (g i)
        HasEtaleFactorization p (stratumMap (algebraMap R S) I (g i)) ∧
          ((p : Rᵢ) = 0 ∨ IsUnit (p : Rᵢ)) := by
  sorry -- noetherian 近似環で spread_out_generic を用い、真に小さい V(g₁) 上の R₀/(g₁) に帰納。
        -- R への底変換の後に両環を被約化し、(pgᵢ,gᵢ) に細分して p 可逆の層と p = 0 の層を得る

end SerrePositivity.CommutativeAlgebra
