module

public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.AdicEuler
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Rees
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Parameters
public import SerrePositivity.CommutativeAlgebra.Koszul.RegularEuler
public import SerrePositivity.CommutativeAlgebra.Koszul.FiniteLength
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Generators
public import SerrePositivity.LengthAlgebra.ConeCompositionEuler
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.BigOperators.Field

/-! # Koszul 重複度の公式

## 概要

Noether 局所環のパラメータ系 `z` について、重複度 `e((z), D)` は Koszul 複体の Euler 標数に等しい
（`multiplicity_eq_chiOrd_koszul`、Stacks 0AZZ）。系として、正則な底の上の有限加群の重複度は階数に等しく、
パラメータの最後の元を冪にした重複度と、Koszul Euler 標数の極限としての重複度を得る。

## 方針

項の Euler 和（`KoszulMultiplicity/AdicEuler`）が十分先で重複度に一致し、Koszul 複体の `I` 進の尾部が十分先で
非輪状（`KoszulMultiplicity/Rees`）なので、項の Euler 和は Koszul ホモロジーの Euler 標数に一致する。

## 規約

名前空間は `KoszulMultiplicity`（証明鎖）と `HilbertSamuel`（系）。CLMST が `multiplicity_eq_chiOrd_koszul` を使う。

## 使われ方

交点重複度の正値性、論文 §2 の長さ代数、CLMST のパラメータの長さ。
-/

@[expose] public noncomputable section

universe u v w

section Proof

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The filtered comparison and the Samuel polynomial computation give multiplicity.
The tail acyclicity is supplied by the Rees Koszul construction. -/
theorem multiplicity_eq_chiOrd_of_eventually_acyclic_adicTail
    {h : ℕ} (z : Fin h → R) (hz : IsSystemOfParameters R z)
    (hd : ∀ q, ((koszulComplex z).d q (q + 1)).hom.range ≤
      Ideal.span (Set.range z) • ⊤)
    (hacyclic : ∀ᶠ n : ℕ in atTop, ∀ q,
      IsZero ((AdicFilteredComplex.tail (koszulComplex z) (Ideal.span (Set.range z)) hd
        (n : ℤ)).homology q)) :
    (HilbertSamuel.multiplicity R (Ideal.span (Set.range z)) R : ℝ) =
      chiOrd (koszulComplex z) := by
  obtain ⟨n, hn, hvalue⟩ :=
    (hacyclic.and (KoszulMultiplicity.eventually_euler_koszul_eq_multiplicity z hz)).exists
  have hf : ∀ q, Module.Finite R ((koszulComplex z).X q) :=
    fun q => (koszulComplex_free_finite_X z q).2
  have hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((koszulComplex z).X q) :=
    ⟨-(h : ℤ), 0, fun q hq => hq.elim
      (koszulComplex_isZero_X_of_lt z q) (koszulComplex_isZero_X_of_pos z q)⟩
  exact ((KoszulMultiplicity.chiOrd_eq_adicEuler (koszulComplex z)
    (Ideal.span (Set.range z)) hd n hz.2 hf hb hn).trans hvalue).symm

/-- The parameter-ideal multiplicity equals the ordinary Koszul Euler characteristic.
All filtered acyclicity and numerical inputs are supplied by the Rees construction. -/
theorem multiplicity_eq_chiOrd_koszul {h : ℕ} (z : Fin h → R)
    (hz : IsSystemOfParameters R z) :
    (HilbertSamuel.multiplicity R (Ideal.span (Set.range z)) R : ℝ) =
      chiOrd (koszulComplex z) :=
  multiplicity_eq_chiOrd_of_eventually_acyclic_adicTail z hz
    (koszulComplex_differential_range_le R (Ideal.span (Set.range z)) z rfl)
    (KoszulMultiplicity.eventually_adicTail_acyclic R (Ideal.span (Set.range z)) z rfl)

end SerrePositivity.KoszulMultiplicity

end Proof

section Formulas

open IsLocalRing
namespace SerrePositivity.HilbertSamuel

set_option backward.isDefEq.respectTransparency false in
/-- 同じ環の上で測った Koszul Euler 数は、通常の複体の Euler 数である。 -/
lemma koszulEulerChar_self (D : Type u) [CommRing D] {r : ℕ} (z : Fin r → D) :
    koszulEulerChar D D z = chiOrd (koszulComplex z) := by
  unfold koszulEulerChar chiOrd
  congr 1

/-- 剰余体への全射があれば、Koszul Euler 数の係数制限は値を変えない。
有限性・単射性・パラメータ条件は、この長さの比較自体には不要。 -/
theorem koszulEulerChar_eq_chiOrd_of_residue_surjective
    (A D : Type u) [CommRing A] [CommRing D] [IsLocalRing D] [Algebra A D]
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) :
    koszulEulerChar A D t = chiOrd (koszulComplex (algebraMap A D ∘ t)) := by
  unfold koszulEulerChar chiOrd
  congr 1
  funext i
  rw [length_restrictScalars_eq hres]

/-- Koszul 重複度公式を、剰余体が一致する有限局所環拡大に沿って係数制限する。
同一環上の公式と長さの移送はともに証明済み。 -/
theorem multiplicity_eq_koszulEulerChar_of_residue_surjective
    (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [Module.Finite A D]
    (_hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) :
    (multiplicity D (Ideal.span (Set.range (algebraMap A D ∘ t))) D : ℝ) =
      koszulEulerChar A D t := by
  rw [koszulEulerChar_eq_chiOrd_of_residue_surjective A D hres t]
  exact KoszulMultiplicity.multiplicity_eq_chiOrd_koszul _ hsop

/-- 正則基底のパラメータに対する重複度は、剰余体が一致すれば基底上の階数に等しい。
証明済みの重複度公式と Euler 特性の階数公式からの導出。 -/
theorem multiplicity_eq_rank_of_regular_base
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdim : ringKrullDim A = h) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) :
    (multiplicity D (Ideal.span (Set.range (algebraMap A D ∘ t))) D : ℝ) =
      Module.finrank A D := by
  rw [multiplicity_eq_koszulEulerChar_of_residue_surjective A D hinj hres t hsop,
    koszulEulerChar_eq_finrank A D t ht hdim]

end SerrePositivity.HilbertSamuel

end Formulas

section LastPower

namespace SerrePositivity
open CategoryTheory Limits IsLocalRing
set_option backward.isDefEq.respectTransparency false

/-- 最後の座標だけを冪にした Koszul 複体は、前の列へのその冪のスカラー錐である。 -/
theorem koszulComplex_last_pow_eq {D : Type u} [CommRing D] {e : ℕ}
    (z : Fin (e + 1) → D) (k : ℕ) :
    koszulComplex (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k)) =
      CochainComplex.mappingCone (smulId (z (Fin.last e) ^ k) (koszulComplex (Fin.init z))) := by
  rw [koszulComplex_succ]
  rw [Fin.snoc_last]
  apply congrArg (fun y : Fin e → D ↦
    CochainComplex.mappingCone (smulId (z (Fin.last e) ^ k) (koszulComplex y)))
  funext j
  exact Fin.snoc_castSucc _ _ j

/-- 最後のパラメータの k 乗による Koszul Euler 数の倍率は k。
前の列のホモロジーに有限長性を仮定せず、各正冪の錐の有限長性を使う。 -/
theorem chiOrd_koszul_last_pow (D : Type u) [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] {e : ℕ} (z : Fin (e + 1) → D)
    (hz : IsSystemOfParameters D z) (k : ℕ) (hk : 0 < k) :
    chiOrd (koszulComplex (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k))) =
      (k : ℝ) * chiOrd (koszulComplex z) := by
  let P := koszulComplex (Fin.init z)
  let a := z (Fin.last e)
  have hb (n : ℕ) (_hn : 0 < n) : ∃ b₁ b₂ : ℤ, ∀ q,
      q < b₁ ∨ b₂ < q → IsZero ((Cone.cone (smulId (a ^ n) P)).X q) := by
    change ∃ b₁ b₂ : ℤ, ∀ q, q < b₁ ∨ b₂ < q →
      IsZero ((CochainComplex.mappingCone
        (smulId (z (Fin.last e) ^ n) (koszulComplex (Fin.init z)))).X q)
    rw [← koszulComplex_last_pow_eq z n]
    exact (isPerfectSupported_koszulComplex
      (Fin.snoc (Fin.init z) (z (Fin.last e) ^ n))).bounded
  have hl (n : ℕ) (hn : 0 < n) (q : ℤ) :
      (NormalizedLength.ordinary D).len ((Cone.cone (smulId (a ^ n) P)).homology q) ≠ ⊤ := by
    rw [NormalizedLength.ordinary_len]
    apply ENat.toENNReal_ne_top.mpr
    apply Module.length_ne_top_iff.mpr
    change IsFiniteLength D ((CochainComplex.mappingCone
      (smulId (z (Fin.last e) ^ n) (koszulComplex (Fin.init z)))).homology q)
    rw [← koszulComplex_last_pow_eq z n]
    exact isFiniteLength_koszulHomology_of_isSystemOfParameters D _ (hz.pow_last n hn) q
  have he := lambdaEuler_scalarCone_pow (NormalizedLength.ordinary D) P a hb
    (fun _ _ _ ↦ IsPowTorsion.bot) hl k hk
  change lambdaEuler (NormalizedLength.ordinary D)
      (CochainComplex.mappingCone (smulId (z (Fin.last e) ^ k) (koszulComplex (Fin.init z)))) =
    (k : ℝ) * lambdaEuler (NormalizedLength.ordinary D)
      (CochainComplex.mappingCone (smulId (z (Fin.last e)) (koszulComplex (Fin.init z)))) at he
  rw [← koszulComplex_last_pow_eq z k, ← koszulComplex_succ z,
    ← chiOrd_eq_lambdaEuler_ordinary, ← chiOrd_eq_lambdaEuler_ordinary] at he
  exact he

namespace HilbertSamuel

/-- 最後のパラメータだけを正の k 乗へ置き換えると、重複度は k 倍となる。
合成錐の共通 Euler 加法性と証明済みの Koszul 重複度公式から導く。 -/
theorem multiplicity_parameter_last_pow (D : Type u) [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] {e : ℕ} (z : Fin (e + 1) → D)
    (hz : IsSystemOfParameters D z) (k : ℕ) (hk : 0 < k) :
    multiplicity D (Ideal.span (Set.range (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k)))) D =
      (k : ℚ) * multiplicity D (Ideal.span (Set.range z)) D := by
  have hreal : (multiplicity D
      (Ideal.span (Set.range (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k)))) D : ℝ) =
      (k : ℝ) * (multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
    rw [KoszulMultiplicity.multiplicity_eq_chiOrd_koszul _ (hz.pow_last k hk),
      KoszulMultiplicity.multiplicity_eq_chiOrd_koszul z hz]
    exact chiOrd_koszul_last_pow D z hz k hk
  exact_mod_cast hreal

end HilbertSamuel

end SerrePositivity

end LastPower

section Limit

namespace SerrePositivity.HilbertSamuel

open IsLocalRing CategoryTheory Filter
open scoped ENNReal

variable (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]

/-- パラメータ系の成分ごとの `q` 乗に対する通常の Euler 数は `q^h e((z), D)`。
二つの証明済み重複度公式を明示的に適用する。 -/
theorem chiOrd_koszul_pow {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (q : ℕ) (hq : 0 < q) :
    chiOrd (koszulComplex (fun j ↦ z j ^ q)) =
      (q : ℝ) ^ h * (multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
  have hp := multiplicity_eq_koszulEulerChar_of_residue_surjective D D
    (show Function.Injective (algebraMap D D) from Function.injective_id)
    (show Function.Surjective ((residue D).comp (algebraMap D D)) from residue_surjective)
    (fun j ↦ z j ^ q) (hz.pow D q hq)
  have he : algebraMap D D ∘ (fun j ↦ z j ^ q) = (fun j ↦ z j ^ q) := funext fun _ ↦ rfl
  rw [he, koszulEulerChar_self, KoszulMultiplicity.multiplicity_parameter_pow D z hz q hq] at hp
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] using hp.symm

omit [IsLocalRing D] [IsNoetherianRing D] in
/-- 通常の Koszul Euler 数は `[-h, 0]` の有限和である。 -/
lemma chiOrd_koszul_eq_sum {h : ℕ} (z : Fin h → D) :
    chiOrd (koszulComplex z) =
      ∑ i ∈ Finset.Icc (-(h : ℤ)) 0,
        ((i.negOnePow : ℤ) : ℝ) *
          ((Module.length D ((koszulComplex z).homology i)).toNat : ℝ) := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  have hi' : i < -(h : ℤ) ∨ 0 < i := by
    simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hn
  have hX : CategoryTheory.Limits.IsZero ((koszulComplex z).X i) := hi'.elim
    (koszulComplex_isZero_X_of_lt z i) (koszulComplex_isZero_X_of_pos z i)
  have := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X _ _ hX)
  exact hi (by simp [Module.length_eq_zero])

/-- 高次 Koszul ホモロジーの正規化長さが零へ収束すれば、パラメータ系の成分ごとの冪で
作った商の正規化長さは重複度へ収束する。冪の列は任意の正の整数列でよい。 -/
theorem normalized_parameter_quotient_tendsto_of_higher_koszul
    {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (q : ℕ → ℕ) (hq : ∀ n, 0 < q n)
    (hlim : ∀ i : ℤ, i < 0 → Tendsto (fun n ↦
      ((Module.length D ((koszulComplex (fun j ↦ z j ^ q n)).homology i)).toNat : ℝ) /
        (q n : ℝ) ^ h) atTop (nhds 0)) :
    Tendsto (fun n ↦
      ((Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ q n))).toNat : ℝ) /
        (q n : ℝ) ^ h) atTop
      (nhds (multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  let s := Finset.Icc (-(h : ℤ)) 0
  let a (n : ℕ) (i : ℤ) :=
    ((Module.length D ((koszulComplex (fun j ↦ z j ^ q n)).homology i)).toNat : ℝ) /
      (q n : ℝ) ^ h
  let f (n : ℕ) (i : ℤ) := ((i.negOnePow : ℤ) : ℝ) * a n i
  have hzero : (0 : ℤ) ∈ s := by simp [s]
  have hsum (n : ℕ) : ∑ i ∈ s, f n i =
      (multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
    have he := congrArg (fun x : ℝ ↦ x / (q n : ℝ) ^ h)
      (chiOrd_koszul_pow D z hz (q n) (hq n))
    rw [chiOrd_koszul_eq_sum, Finset.sum_div] at he
    have hne : (q n : ℝ) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast (hq n).ne')
    simpa only [s, f, a, mul_div_assoc, mul_div_cancel_left₀ _ hne] using he
  have herror : Tendsto (fun n ↦ ∑ i ∈ s.erase 0, f n i) atTop (nhds 0) := by
    have hl : ∀ i ∈ s.erase 0, Tendsto (fun n ↦ f n i) atTop (nhds (0 : ℝ)) := by
      intro i hi
      have hi' : i < 0 := lt_of_le_of_ne
        (Finset.mem_Icc.mp (Finset.mem_erase.mp hi).2).2 (Finset.mem_erase.mp hi).1
      simpa only [mul_zero] using (hlim i hi').const_mul ((i.negOnePow : ℤ) : ℝ)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (s.erase 0) hl
  have hterm (n : ℕ) : a n 0 =
      (multiplicity D (Ideal.span (Set.range z)) D : ℝ) - ∑ i ∈ s.erase 0, f n i := by
    have he := Finset.sum_erase_add s (f n) hzero
    rw [hsum] at he
    have hf : f n 0 = a n 0 := by simp [f]
    rw [hf] at he
    linarith
  have hmain : Tendsto (fun n ↦ a n 0) atTop
      (nhds (multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
    simpa only [hterm, sub_zero] using tendsto_const_nhds.sub herror
  have hquot (n : ℕ) : a n 0 =
      ((Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ q n))).toNat : ℝ) /
        (q n : ℝ) ^ h := by
    dsimp only [a]
    rw [(koszulComplex_homology_zero_equiv (fun j ↦ z j ^ q n)).some.length_eq]
  simpa only [hquot] using hmain

/-- 前の極限比較を、正規化長さと同じ値域 `ℝ≥0∞` で述べる。
有限長性・重複度の非負性を確認して実数値の極限と往復する。 -/
theorem normalized_parameter_quotient_tendsto_ennreal_of_higher_koszul
    {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (q : ℕ → ℕ) (hq : ∀ n, 0 < q n)
    (hlim : ∀ i : ℤ, i < 0 → Tendsto (fun n ↦
      (Module.length D ((koszulComplex (fun j ↦ z j ^ q n)).homology i) : ℝ≥0∞) /
        (q n : ℝ≥0∞) ^ h) atTop (nhds 0)) :
    Tendsto (fun n ↦
      (Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ q n)) : ℝ≥0∞) /
        (q n : ℝ≥0∞) ^ h) atTop
      (nhds (ENNReal.ofReal (multiplicity D (Ideal.span (Set.range z)) D : ℝ))) := by
  have hreal := normalized_parameter_quotient_tendsto_of_higher_koszul D z hz q hq
    (fun i hi ↦ by
      have he := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp (hlim i hi)
      simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
        toReal_toENNReal, ENNReal.toReal_zero] using he)
  have hfinite n : Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ q n)) ≠ ⊤ := by
    rw [← (koszulComplex_homology_zero_equiv (fun j ↦ z j ^ q n)).some.length_eq]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_koszulHomology_of_isSystemOfParameters D _ (hz.pow D _ (hq n)) 0)
  have hepos : 0 ≤ (multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
    exact_mod_cast (multiplicity_pos D _ hz.2).le
  apply (ENNReal.tendsto_toReal_iff (fun n ↦ ENNReal.div_ne_top
    (ENat.toENNReal_ne_top.mpr (hfinite n))
    (pow_ne_zero h (by exact_mod_cast (hq n).ne'))) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    toReal_toENNReal, ENNReal.toReal_ofReal hepos] using hreal

end SerrePositivity.HilbertSamuel

end Limit
