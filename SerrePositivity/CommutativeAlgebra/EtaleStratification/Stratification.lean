module

public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Basic
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
  sorry -- Algebra.FormallyEtale.of_isSeparable と有限体拡大の有限表示性

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
  sorry -- 指定した係数と有限表示の関係式・各生成元のモニック関係の係数で R₀ を生成し、同じ表示で S₀ を作る

/-- 全商環の因子は基底の極小点で添字づける。 -/
abbrev GenericPoint (R : Type u) [CommRing R] :=
  {P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R}

abbrev GenericField {R : Type u} [CommRing R] (P : GenericPoint R) := P.val.asIdeal.ResidueField
abbrev GenericProduct (R : Type u) [CommRing R] := ∀ P : GenericPoint R, GenericField P

def genericProductMap (R : Type u) [CommRing R] : R →+* GenericProduct R :=
  RingHom.pi (fun P => algebraMap R (GenericField P))

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
            (algebraMap (GenericField (v j)) (L j)).comp (Pi.evalRingHom GenericField (v j)))).toAlgebra
          Nonempty (((GenericProduct R ⊗[R] S) ⧸ nilradical (GenericProduct R ⊗[R] S))
            ≃ₐ[GenericProduct R] (∀ j, L j)) ∧
            ∀ j,
              let k := GenericField (v j)
              let M := separableClosure k (L j)
              FiniteDimensional k (L j) ∧ Module.Finite k M ∧ Algebra.Etale k M ∧
                IsPurelyInseparable M (L j) ∧
                (IsUnit (p : k) → Function.Bijective (algebraMap M (L j))) := by
  sorry -- 極小点は有限。K 上の有限被約代数を体の積に分け、各有限拡大で相対分離閉包を取る。
        -- p 可逆の剰余体は hZp で全素数が単元なので標数 0

/-- V(I) の被約構造上で g を反転する。R/√I は (R/I)_red の標準表示。 -/
abbrev StratumRing {R : Type u} [CommRing R] (I : Ideal R) (g : R) :=
  Localization.Away (Ideal.Quotient.mk I.radical g)

def stratumUnit {R : Type u} [CommRing R] (I : Ideal R) (g : R) : R →+* StratumRing I g :=
  (algebraMap (R ⧸ I.radical) (StratumRing I g)).comp (Ideal.Quotient.mk I.radical)

/-- S では先に I を延長し、その後に根基を取って局所化する。 -/
def stratumMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R) (g : R) :
    StratumRing I g →+* StratumRing (I.map f) (f g) := by
  let J := I.map f
  let q : R ⧸ I.radical →+* S ⧸ J.radical := Ideal.quotientMap J.radical f
    (Ideal.map_le_iff_le_comap.mp (Ideal.map_radical_le f))
  exact IsLocalization.Away.lift (Ideal.Quotient.mk I.radical g)
    (g := (algebraMap (S ⧸ J.radical) (StratumRing J (f g))).comp q)
    (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk J.radical (f g)))

/-- f の p 反転で誘導される射。 -/
def invertPrimeMap {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) (f : A →+* B) :
    Localization.Away (p : A) →+* Localization.Away (p : B) := by
  letI : IsLocalization.Away (f (p : A)) (Localization.Away (p : B)) := by
    rw [map_natCast]; infer_instance
  exact IsLocalization.Away.map _ _ f (p : A)

/-- 指定した射 f 自身を有限エタール射と普遍同相に分解する。 -/
def HasEtaleFactorization {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) (f : A →+* B) : Prop :=
  ∃ (T : CommRingCat.{u}) (a : A →+* T) (b : T →+* B),
    letI : Algebra A T := a.toAlgebra
    b.comp a = f ∧ Module.Finite A T ∧ Algebra.Etale A T ∧ IsUniversalHomeomorphism b ∧
      Function.Bijective (invertPrimeMap p b)

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

/-- 第 i 層より前に現れる元だけが生成するイデアル。初層では零イデアル。 -/
def earlierIdeal {R : Type u} [CommRing R] {n : ℕ} (g : Fin n → R) (i : Fin n) : Ideal R :=
  Ideal.span (g '' {j | j < i})

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
