module

public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import SerrePositivity.CommutativeAlgebra.Unmixedness
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Data.Set.List
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite

/-! # 素イデアル回避によるパラメータの選択（論文 §5.2 の (5.4)）

## 概要

正則局所環 `R`（次元 `d`）の素イデアル `P`、`Q` が `dim R/P = h`、`dim R/Q = l`、`h + l = d`、
`√(P + Q) = m_R` をみたすとき、`x_1, …, x_h ∈ Q` で、`R` 正則列かつ像が `R/P` のパラメータ系
（`√(P + (x)) = m_R`）となるものがある（`exists_regular_parameters_in`）。

## 方針（論文 §5.2）

`x_1, …, x_i` まで選んだとき、次の二種類の素イデアルを避けて `x_{i+1} ∈ Q` をとる。

1. `R/(x_1, …, x_i)` の随伴素イデアル `p`：非混合性（`Unmixedness`）により
   `dim R/p = d − i > l = dim R/Q` なので `Q ⊄ p`。避ければ `x_{i+1}` は非零因子。
2. `P + (x_1, …, x_i)` の極小素イデアル `p`：`Q ⊆ p` なら `P + Q ⊆ p` で `p = m_R`、すると
   `R/(P + (x))` の素イデアルは `m_R` だけで次元 `0` だが、実際の次元は `h − i > 0`。
   避ければ次元がちょうど `1` 下がる（Mathlib の `supportDim_quotSMulTop_succ_eq_...`）。

有限個の素イデアルに含まれない `Q` の元は素イデアル回避（`Ideal.subset_union_prime`）で存在する。

## 規約

非混合性の入力は `Unmixedness` の証明済みの定理で、未証明の入力は使わない。

## 使われ方

論文 §5 のパラメータの選択（`Paper/Section5/ParameterChoice`）。
-/

@[expose] public noncomputable section

universe u v w

open IsLocalRing PrimeSpectrum RingTheory.Sequence

namespace SerrePositivity

section Avoidance

section regular

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **一歩**：弱正則列 `rs`（長さ `i`、`i + l < d`）で `dim R/(P + (rs)) > 0` なら、`y ∈ Q` で
`rs ++ [y]` も弱正則列、`dim R/(P + (rs, y)) + 1 = dim R/(P + (rs))` となるものがある。 -/
lemma exists_avoiding_step (P Q : Ideal R) [hQ : Q.IsPrime] {l d : ℕ}
    (hd : ringKrullDim R = d) (hQdim : ringKrullDim (R ⧸ Q) = l)
    (hPQ : (P ⊔ Q).radical = maximalIdeal R) (rs : List R) (hrs : IsWeaklyRegular R rs)
    (hlt : rs.length + l < d) (hpos : 0 < ringKrullDim (R ⧸ (P ⊔ Ideal.ofList rs))) :
    ∃ y ∈ Q, IsWeaklyRegular R (rs ++ [y]) ∧
      ringKrullDim (R ⧸ (P ⊔ Ideal.ofList (rs ++ [y]))) + 1 =
        ringKrullDim (R ⧸ (P ⊔ Ideal.ofList rs)) := by
  classical
  set I := P ⊔ Ideal.ofList rs with hI
  have hfin : (associatedPrimes R (R ⧸ Ideal.ofList rs) ∪ I.minimalPrimes).Finite :=
    (associatedPrimes.finite R _).union I.finite_minimalPrimes_of_isNoetherianRing
  let s := hfin.toFinset
  have hprime : ∀ p ∈ s, p.IsPrime := by
    intro p hp
    rcases hfin.mem_toFinset.mp hp with hp | hp
    · exact hp.isPrime
    · exact hp.1.1
  -- `Q` はどの回避すべき素イデアルにも含まれない
  have hnot : ∀ p ∈ s, ¬ Q ≤ p := by
    intro p hp hQp
    rcases hfin.mem_toFinset.mp hp with hp | hp
    · -- 随伴素イデアル：次元の比較
      have h1 := ringKrullDim_quotient_add_length_of_mem_associatedPrimes rs hrs hp
      have h2 : ringKrullDim (R ⧸ p) ≤ ringKrullDim (R ⧸ Q) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hQp)
          (Ideal.Quotient.factor_surjective hQp)
      rw [hd] at h1
      rw [hQdim] at h2
      have h3 : ((d : ℕ) : WithBot ℕ∞) ≤ ((l + rs.length : ℕ) : WithBot ℕ∞) := by
        rw [← h1, Nat.cast_add]
        exact add_le_add_left h2 _
      have h4 : d ≤ l + rs.length := by exact_mod_cast h3
      omega
    · -- 極小素イデアル：`p = m` となり次元 `0` に矛盾
      have hIp : I ≤ p := hp.1.2
      have hPp : P ≤ p := le_sup_left.trans hIp
      have hmp : maximalIdeal R ≤ p := by
        rw [← hPQ, ← hp.1.1.radical]
        exact Ideal.radical_mono (sup_le hPp hQp)
      have hzero : ringKrullDim (R ⧸ I) ≤ 0 := by
        rw [ringKrullDim_quotient]
        refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun q q' hqq' ↦ ?_
        have hq : I ≤ q.1.asIdeal := q.2
        have hpq : p ≤ q.1.asIdeal :=
          hp.2 ⟨q.1.isPrime, hq⟩ ((le_maximalIdeal q.1.isPrime.ne_top).trans hmp)
        exact (le_maximalIdeal q'.1.isPrime.ne_top).trans (hmp.trans hpq)
      exact absurd hpos (not_lt.mpr hzero)
  have hsub : ¬ ((Q : Set R) ⊆ ⋃ p ∈ (↑s : Set (Ideal R)), ((fun p : Ideal R ↦ p) p : Set R)) := by
    rw [Ideal.subset_union_prime ⊥ ⊥ (fun p hp _ _ ↦ hprime p hp)]
    rintro ⟨p, hp, hQp⟩
    exact hnot p hp hQp
  obtain ⟨y, hyQ, hy⟩ := Set.not_subset.mp hsub
  simp only [Set.mem_iUnion, not_exists] at hy
  have hyas : ∀ p ∈ associatedPrimes R (R ⧸ Ideal.ofList rs), y ∉ p :=
    fun p hp ↦ hy p (hfin.mem_toFinset.mpr (Or.inl hp))
  have hymin : ∀ p ∈ I.minimalPrimes, y ∉ p :=
    fun p hp ↦ hy p (hfin.mem_toFinset.mpr (Or.inr hp))
  have hym : y ∈ maximalIdeal R := le_maximalIdeal hQ.ne_top hyQ
  refine ⟨y, hyQ, ?_, ?_⟩
  · have hreg : IsSMulRegular (R ⧸ Ideal.ofList rs) y := by
      by_contra hc
      have : y ∈ ⋃ p ∈ associatedPrimes R (R ⧸ Ideal.ofList rs), (p : Set R) := by
        rw [biUnion_associatedPrimes_eq_compl_regular]
        exact hc
      simp only [Set.mem_iUnion] at this
      obtain ⟨p, hp, hyp⟩ := this
      exact hyas p hp hyp
    rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff]
    refine ⟨hrs, ?_⟩
    have heq : (Ideal.ofList rs • ⊤ : Submodule R R) = Ideal.ofList rs := by
      rw [smul_eq_mul, Ideal.mul_top]
    exact ((Submodule.quotEquivOfEq _ _ heq).isSMulRegular_congr y).mpr hreg
  · have h := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
      (M := R ⧸ I) (by rwa [Ideal.annihilator_quotient]) hym
    rw [supportDim_quotSMulTop_quotient, Module.supportDim_quotient_eq_ringKrullDim] at h
    rwa [Ideal.ofList_append, Ideal.ofList_singleton, ← sup_assoc]

/-- **帰納法**：`i ≤ h` について、`Q` の元からなる長さ `i` の弱正則列 `rs` で
`dim R/(P + (rs)) + i = h` となるものがある。 -/
lemma exists_avoiding_list (P Q : Ideal R) [Q.IsPrime] {h l d : ℕ}
    (hd : ringKrullDim R = d) (hPdim : ringKrullDim (R ⧸ P) = h)
    (hQdim : ringKrullDim (R ⧸ Q) = l) (hhl : h + l = d)
    (hPQ : (P ⊔ Q).radical = maximalIdeal R) :
    ∀ i ≤ h, ∃ rs : List R, rs.length = i ∧ (∀ r ∈ rs, r ∈ Q) ∧ IsWeaklyRegular R rs ∧
      ringKrullDim (R ⧸ (P ⊔ Ideal.ofList rs)) + i = h := by
  intro i hi
  induction i with
  | zero => exact ⟨[], rfl, by simp, .nil R R,
    by
      have hnil : P ⊔ Ideal.ofList ([] : List R) = P := by
        rw [Ideal.ofList_nil, sup_bot_eq]
      rw [hnil, Nat.cast_zero, add_zero, hPdim]⟩
  | succ i ih =>
    obtain ⟨rs, hlen, hQ', hrs, hdim⟩ := ih (by omega)
    have hpos : 0 < ringKrullDim (R ⧸ (P ⊔ Ideal.ofList rs)) := by
      by_contra hc
      have h1 := add_le_add_left (not_lt.mp hc) (i : WithBot ℕ∞)
      rw [hdim, zero_add] at h1
      have : h ≤ i := by exact_mod_cast h1
      omega
    obtain ⟨y, hyQ, hreg, hy⟩ := exists_avoiding_step P Q hd hQdim hPQ rs hrs (by omega) hpos
    refine ⟨rs ++ [y], by simp [hlen], ?_, hreg, ?_⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hQ' r hr
      · rw [List.mem_singleton.mp hr]
        exact hyQ
    · rw [← hdim, ← hy, Nat.cast_succ, add_comm (i : WithBot ℕ∞) 1, add_assoc]

/-- **(5.4)**：正則局所環 `R`（`dim R = d`）の素イデアル `P`、`Q` で `dim R/P = h`、`dim R/Q = l`、
`h + l = d`、`√(P + Q) = m_R` なら、`x_1, …, x_h ∈ Q` で `R` 弱正則列かつ
`√(P + (x)) = m_R`（像が `R/P` のパラメータ系）となるものがある。 -/
theorem exists_regular_parameters_in (P Q : Ideal R) [Q.IsPrime] {h l d : ℕ}
    (hd : ringKrullDim R = d) (hPdim : ringKrullDim (R ⧸ P) = h)
    (hQdim : ringKrullDim (R ⧸ Q) = l) (hhl : h + l = d)
    (hPQ : (P ⊔ Q).radical = maximalIdeal R) :
    ∃ x : Fin h → R, (∀ i, x i ∈ Q) ∧ IsWeaklyRegular R (List.ofFn x) ∧
      (P ⊔ Ideal.span (Set.range x)).radical = maximalIdeal R := by
  obtain ⟨rs, hlen, hQ', hrs, hdim⟩ := exists_avoiding_list P Q hd hPdim hQdim hhl hPQ h le_rfl
  subst hlen
  refine ⟨rs.get, fun i ↦ hQ' _ (List.get_mem _ _), by rwa [List.ofFn_get], ?_⟩
  have hspan : Ideal.span (Set.range rs.get) = Ideal.ofList rs := by
    rw [Ideal.ofList, Set.range_list_get]
  rw [hspan]
  refine (radical_eq_maximalIdeal_iff_ringKrullDim_quotient_le_zero ?_).mpr (le_of_eq ?_)
  · intro htop
    have : Subsingleton (R ⧸ (P ⊔ Ideal.ofList rs)) := Ideal.Quotient.subsingleton_iff.mpr htop
    rw [ringKrullDim_eq_bot_of_subsingleton, WithBot.bot_add] at hdim
    exact WithBot.bot_ne_coe hdim
  -- `D + n = n` から `D = 0`
  set D := ringKrullDim (R ⧸ (P ⊔ Ideal.ofList rs))
  have hne : D ≠ ⊥ := by
    intro hD
    rw [hD, WithBot.bot_add] at hdim
    exact WithBot.bot_ne_coe hdim
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← he] at hdim ⊢
  have : e + rs.length = rs.length := by exact_mod_cast hdim
  have he0 : e = 0 := by
    induction e using ENat.recTopCoe with
    | top => simp at this
    | coe m =>
      have : m + rs.length = rs.length := by exact_mod_cast this
      have hm : m = 0 := by omega
      rw [hm]
      rfl
  rw [he0]
  rfl

end regular

end Avoidance

section FiniteExtension

open IsLocalRing

/-- 正則局所環 R の素イデアル P・Q で P + Q の根基が極大イデアルなら、Q の中に R の正則列 x を選び、
その像を R/P 上の有限拡大 D のパラメータ系にできる（論文 (5.4) のパラメータの選択）。 -/
theorem exists_regular_parameters_for_finite_extension
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (D : Type u) [CommRing D] [IsLocalRing D]
    [Algebra R D] [Algebra (R ⧸ P) D] [IsScalarTower R (R ⧸ P) D]
    [Module.Finite (R ⧸ P) D] (hinj : Function.Injective (algebraMap (R ⧸ P) D))
    {h e : ℕ} (hd : ringKrullDim R = (e + h : ℕ))
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = e)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R) :
    ∃ x : Fin h → R, (∀ i, x i ∈ Q) ∧
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) ∧
      IsSystemOfParameters D (algebraMap R D ∘ x) := by
  let : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  obtain ⟨x, hxQ, hxreg, hxrad⟩ := exists_regular_parameters_in P Q hd hPdim hQdim
    (Nat.add_comm h e) hprimary
  have hx := isSystemOfParameters_quotient_of_radical P x hPdim hxrad
  have hxD := hx.map_finite D hinj
  have hw : algebraMap (R ⧸ P) D ∘ (Ideal.Quotient.mk P ∘ x) =
      algebraMap R D ∘ x := by
    ext i
    exact (IsScalarTower.algebraMap_apply R (R ⧸ P) D (x i)).symm
  rw [hw] at hxD
  exact ⟨x, hxQ, hxreg, hxD⟩

end FiniteExtension

end SerrePositivity
