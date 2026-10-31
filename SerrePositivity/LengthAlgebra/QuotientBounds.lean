module

public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.Analysis.SpecificLimits.Basic
public import SerrePositivity.CommutativeAlgebra.Length.QuotientPower
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.LengthAlgebra.Normalized

/-! # 正規化長さの上界と有限性

## 概要

幾何的に減少する上界から正規化長さ零を導き、巡回商の冪フィルトレーションで正規化長さを抑える（零因子を許す）。パラメータ商のさらに大きな商の有限性と冪ねじれ性、有限生成な冪ねじれ加群の長さの有限性、正の長さを持つ加群の係数環の非自明性を与える。

## 方針

有限段の長さは拡張非負実数のまま扱い、無限大を実数の零へ落とさない。有限性は有限個の巡回像と長さの劣加法性で移す。

## 規約

環の Noether 性や `HasSup` は要らない。

## 使われ方

CLMST の幾何的減衰の評価、Paper の長さ代数の構成。
-/

@[expose] public noncomputable section

universe u

section GeometricDecayPart

namespace SerrePositivity
open Filter Topology
open scoped ENNReal

/-- 有限な定数と比率1未満の冪による上界があれば、拡張非負実数値は零。 -/
theorem ennreal_eq_zero_of_geometric_bound (a c r : ℝ≥0∞) (hc : c ≠ ⊤) (hr : r < 1)
    (hbound : ∀ n : ℕ, a ≤ c * r ^ n) : a = 0 := by
  have hlim : Tendsto (fun n : ℕ ↦ c * r ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr hc)
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) bot_le

/-- 指数的に増大する分母で割った一様な有限上界から零を導く。 -/
theorem ennreal_eq_zero_of_div_pow_bound (a c r : ℝ≥0∞) (hc : c ≠ ⊤) (hr : 1 < r)
    (hbound : ∀ n : ℕ, a ≤ c / r ^ n) : a = 0 := by
  apply ennreal_eq_zero_of_geometric_bound a c r⁻¹ hc
    (ENNReal.inv_lt_one.mpr hr)
  simpa only [div_eq_mul_inv, ENNReal.inv_pow] using hbound

namespace NormalizedLength
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 巡回商のイデアルを拡大すると、冪ねじれな源の長さ以下になる。 -/
theorem len_quotient_le_of_pow_le (n : ℕ) (I K : Ideal R) (hJI : J ^ n ≤ I)
    (hIK : I ≤ K) : lam.len (R ⧸ K) ≤ lam.len (R ⧸ I) := by
  have htor : IsPowTorsion J (R ⧸ I) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    exact hJI
  exact lam.len_le_of_surjective (Ideal.Quotient.factorₐ R hIK).toLinearMap
    (Ideal.Quotient.factor_surjective hIK) htor

/-- 冪ねじれな巡回商を幾何的に小さい巡回商から覆えば、目的の長さは零。 -/
theorem len_quotient_eq_zero_of_geometric_covers
    (n : ℕ) (K : Ideal R) (I : ℕ → Ideal R)
    (hJI : ∀ m, J ^ n ≤ I m) (hIK : ∀ m, I m ≤ K)
    (c r : ℝ≥0∞) (hc : c ≠ ⊤) (hr : r < 1)
    (hbound : ∀ m, lam.len (R ⧸ I m) ≤ c * r ^ m) : lam.len (R ⧸ K) = 0 :=
  ennreal_eq_zero_of_geometric_bound _ c r hc hr fun m ↦
    (lam.len_quotient_le_of_pow_le n (I m) K (hJI m) (hIK m)).trans (hbound m)

/-- 一様な冪ねじれ条件と指数的な分母による巡回商の上界から長さ零を得る。 -/
theorem len_quotient_eq_zero_of_div_pow_covers
    (n : ℕ) (K : Ideal R) (I : ℕ → Ideal R)
    (hJI : ∀ m, J ^ n ≤ I m) (hIK : ∀ m, I m ≤ K)
    (c r : ℝ≥0∞) (hc : c ≠ ⊤) (hr : 1 < r)
    (hbound : ∀ m, lam.len (R ⧸ I m) ≤ c / r ^ m) : lam.len (R ⧸ K) = 0 :=
  ennreal_eq_zero_of_div_pow_bound _ c r hc hr fun m ↦
    (lam.len_quotient_le_of_pow_le n (I m) K (hJI m) (hIK m)).trans (hbound m)

end NormalizedLength
end SerrePositivity

end GeometricDecayPart

section QuotientPowerBoundPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.NormalizedLength
open scoped ENNReal
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 固定した関係式がJの冪を含めば、それに任意の関係式を加えた商も冪ねじれ。 -/
theorem isPowTorsion_quotient_sup (I : Ideal R) (n : ℕ) (hJI : J ^ n ≤ I)
    (H : Ideal R) : IsPowTorsion J (R ⧸ (I ⊔ H)) := by
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
    Ideal.annihilator_quotient]
  exact hJI.trans le_sup_left

/-- 一つの関係式を積に置き換えた商の正規化長さは、二つの商の長さの和以下。 -/
theorem len_quotient_sup_span_mul_le (I : Ideal R) (n : ℕ) (hJI : J ^ n ≤ I)
    (x y : R) :
    lam.len (R ⧸ (I ⊔ Ideal.span {x * y})) ≤
      lam.len (R ⧸ (I ⊔ Ideal.span {x})) + lam.len (R ⧸ (I ⊔ Ideal.span {y})) :=
  lam.len_le_add_of_exact (quotientSupSpanMulMap R I x y)
    (quotientSupSpanMulProjection R I x y) (quotientSupSpanMul_exact R I x y)
    (isPowTorsion_quotient_sup I n hJI _) (isPowTorsion_quotient_sup I n hJI _)
    (isPowTorsion_quotient_sup I n hJI _)

/-- 一つの関係式をk乗に置き換えた商の正規化長さは高々k倍。 -/
theorem len_quotient_sup_span_pow_le (I : Ideal R) (n : ℕ) (hJI : J ^ n ≤ I)
    (x : R) (k : ℕ) :
    lam.len (R ⧸ (I ⊔ Ideal.span {x ^ k})) ≤
      (k : ℝ≥0∞) * lam.len (R ⧸ (I ⊔ Ideal.span {x})) := by
  induction k with
  | zero =>
      rw [pow_zero, Ideal.span_singleton_one, sup_top_eq, Nat.cast_zero, zero_mul]
      exact le_of_eq (lam.len_eq_zero_of_subsingleton _)
  | succ k ih =>
      calc
        _ ≤ lam.len (R ⧸ (I ⊔ Ideal.span {x ^ k})) +
            lam.len (R ⧸ (I ⊔ Ideal.span {x})) := by
          rw [pow_succ]
          exact lam.len_quotient_sup_span_mul_le I n hJI (x ^ k) x
        _ ≤ _ := by
          simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
            add_le_add ih (le_refl (lam.len (R ⧸ (I ⊔ Ideal.span {x}))))

/-- xのk乗が既存の関係式に入るとき、xを追加した商のk倍で元の商を上から評価できる。 -/
theorem len_quotient_le_mul_of_pow_mem (I : Ideal R) (n : ℕ) (hJI : J ^ n ≤ I)
    (x : R) (k : ℕ) (hx : x ^ k ∈ I) :
    lam.len (R ⧸ I) ≤ (k : ℝ≥0∞) * lam.len (R ⧸ (I ⊔ Ideal.span {x})) := by
  have heq : I ⊔ Ideal.span {x ^ k} = I :=
    sup_eq_left.mpr ((I.span_singleton_le_iff_mem).mpr hx)
  rw [← lam.len_congr (R ⧸ (I ⊔ Ideal.span {x ^ k})) (R ⧸ I)
    (Ideal.quotientEquivAlgOfEq R heq).toLinearEquiv]
  exact lam.len_quotient_sup_span_pow_le I n hJI x k

end SerrePositivity.NormalizedLength

end QuotientPowerBoundPart

section QuotientBoundsPart

namespace SerrePositivity.LengthAlgebra

open scoped ENNReal

variable {C : Type u} [CommRing C] {J : Ideal C}
  (lam : NormalizedLength C J) (hfg : J.FG) {e : ℕ} (z : Fin e → C)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical) (Q : Ideal C)
  (hzQ : Ideal.span (Set.range z) ≤ Q)

include hfg hJ hzQ in
/-- パラメータを消す商は、長さの定義域である冪ねじれ条件を満たす。 -/
lemma quotient_isPowTorsion_of_span_le : IsPowTorsion J (C ⧸ Q) := by
  apply IsPowTorsion.of_le_radical_annihilator hfg
  rw [Ideal.annihilator_quotient]
  exact hJ.trans (Ideal.radical_mono hzQ)

include hfg hJ hzQ in
/-- パラメータ商からの全射により、下界に使う商の長さも制御できる。 -/
lemma length_quotient_le_of_span_le :
    lam.len (C ⧸ Q) ≤ lam.len (C ⧸ Ideal.span (Set.range z)) := by
  apply lam.len_le_of_surjective (Ideal.Quotient.factorₐ C hzQ).toLinearMap
    (Ideal.Quotient.factor_surjective hzQ)
  exact quotient_isPowTorsion_of_span_le hfg z hJ _ le_rfl

include hfg hJ hzQ in
/-- Koszul 有限性は、パラメータを消す任意の商の長さの有限性を含意する。 -/
lemma length_quotient_ne_top_of_koszul_finite (hfin : KoszulFinite lam z) :
    lam.len (C ⧸ Q) ≠ ⊤ := by
  have hzero : lam.len ((koszulComplex z).homology 0) ≠ ⊤ := by
    have hz : (fun j ↦ z j ^ 1) = z := funext fun j ↦ pow_one (z j)
    exact (congrArg (fun w ↦ lam.len ((koszulComplex w).homology (0 : ℤ)) ≠ ⊤) hz).mp
      (hfin 1 one_pos 0)
  have hquot : lam.len (C ⧸ Ideal.span (Set.range z)) ≠ ⊤ := by
    rwa [lam.len_congr _ _ (koszulComplex_homology_zero_equiv z).some] at hzero
  exact ne_top_of_le_ne_top hquot (length_quotient_le_of_span_le lam hfg z hJ Q hzQ)

end SerrePositivity.LengthAlgebra

end QuotientBoundsPart

section FinitelyGeneratedFiniteLengthPart

namespace SerrePositivity.NormalizedLength
variable {R M : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
    [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- 全ての冪商の長さが有限なら、有限生成な冪ねじれ加群の長さも有限。 -/
theorem len_ne_top_of_finite_of_powQuotient_ne_top
    (hquot : ∀ n : ℕ, lam.len (R ⧸ J ^ n) ≠ ⊤) (hM : IsPowTorsion J M) : lam.len M ≠ ⊤ := by
  obtain ⟨n, hn⟩ := hM
  have hann : J ^ n ≤ Module.annihilator R M := by
    have h := hn
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe] at h
    exact h
  have htquot : IsPowTorsion J (R ⧸ J ^ n) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
  let f (x : M) : R ⧸ J ^ n →ₗ[R] M :=
    (J ^ n).liftQ (LinearMap.toSpanSingleton R M x) (fun r hr ↦ by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Module.mem_annihilator.mp (hann hr) x)
  let V (x : M) := LinearMap.range (f x)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  have htop : s.sup V = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    apply (Finset.le_sup hx : V x ≤ s.sup V)
    refine ⟨Submodule.Quotient.mk 1, ?_⟩
    change (1 : R) • x = x
    exact one_smul R x
  have hle := lam.len_finset_sup_le ⟨n, hn⟩ s V
  rw [← Finset.sup_eq_iSup, htop,
    ← lam.len_congr M (⊤ : Submodule R M) Submodule.topEquiv.symm] at hle
  apply ne_top_of_le_ne_top ?_ hle
  apply ENNReal.sum_ne_top.mpr
  intro x hx
  exact ne_top_of_le_ne_top (hquot n) (lam.len_range_le (f x) htquot)

end SerrePositivity.NormalizedLength

end FinitelyGeneratedFiniteLengthPart

section NontrivialPart

namespace SerrePositivity.NormalizedLength

/-- 正の長さをもつ加群が存在すれば、係数環は非自明である。 -/
lemma nontrivial_ring_of_len_pos
    {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)
    (M : Type u) [AddCommGroup M] [Module C M] (hM : 0 < lam.len M) : Nontrivial C := by
  by_contra hC
  have : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
  have : Subsingleton M := Module.subsingleton C M
  exact hM.ne' (lam.len_eq_zero_of_subsingleton M)

end SerrePositivity.NormalizedLength

end NontrivialPart
