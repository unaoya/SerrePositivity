module

public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Graded
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # 正則局所環の正則系と整域性

## 概要

正則局所環 `R` で、極大イデアルを次元と同数の元 `z` で生成すると `z` は弱正則列
（`isWeaklyRegular_of_span_eq_maximalIdeal`、Stacks 00NQ）。そのような列は常に選べ
（`exists_regular_generators`・`exists_regular_generators_fin`）、正則局所環は整域
（instance `isDomain_of_isRegularLocalRing`）。先頭の元で割った商は次元が一つ低い正則局所環
（`isRegularLocalRing_quotient_head_and_dim`）。

## 方針

列の長さの帰納法。先頭の正則性は随伴次数環の表示の単射性から（`RegularLocalRing/Graded`）、
先頭で割った商の正則局所性は生成数と次元の不等式だけから（Mathlib の
`ringKrullDim_le_ringKrullDim_quotSMulTop_succ`、`ringKrullDim_le_spanFinrank_maximalIdeal`）。
整域性は `isDomain_of_regular_generators`（`RegularSequence`）。

## 規約

`IsRegularLocalRing` は Mathlib の定義（`spanFinrank (maximalIdeal R) = ringKrullDim R`）。
Mathlib への提出候補（mathlib-upstream の G11）。

## 使われ方

正則局所環を使う全ての箇所（論文 §2・§4・§5、正規性・次元・局所化、CLMST、RootTower）。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

section Quotient

open scoped Pointwise

variable {R : Type*} [CommRing R]

/-- 有限族が生成するイデアルの最小生成数は、族の長さ以下である。 -/
private theorem spanFinrank_span_range_le {e : ℕ} (z : Fin e → R) :
    (Ideal.span (Set.range z)).spanFinrank ≤ e := by
  classical
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans
  rw [← Set.image_univ]
  simpa using (Set.ncard_image_le (f := z) (s := Set.univ))

variable [IsLocalRing R]

/-- 生成族の先頭が生成するイデアルは proper である。 -/
theorem span_head_ne_top {e : ℕ} (z : Fin (e + 1) → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R) :
    Ideal.span {z 0} ≠ ⊤ := by
  apply ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
  rw [Ideal.span_singleton_le_iff_mem]
  exact hz ▸ Ideal.subset_span (Set.mem_range_self 0)

/-- 先頭で割った後は、残りの生成元の像が商の極大イデアルを生成する。 -/
theorem span_tail_quotient_eq_maximalIdeal {e : ℕ} (z : Fin (e + 1) → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {z 0})] :
    Ideal.span (Set.range (fun i : Fin e ↦
      Ideal.Quotient.mk (Ideal.span {z 0}) (z i.succ))) =
      maximalIdeal (R ⧸ Ideal.span {z 0}) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {z 0}))
    Ideal.Quotient.mk_surjective, ← hz, Fin.range_fin_succ, Ideal.span_insert,
    Ideal.map_sup]
  have hzero : (Ideal.span {z 0}).map (Ideal.Quotient.mk (Ideal.span {z 0})) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  rw [hzero, bot_sup_eq, Ideal.map_span]
  congr 1
  exact Set.range_comp _ (Fin.tail z)

variable [IsNoetherianRing R]

/-- 先頭で割った商が正則局所環で次元が一つ小さいことは、生成数と次元の
不等式だけから従う。ここでは元の環の正則局所性の型クラスも必要ない。 -/
theorem isRegularLocalRing_quotient_head_and_dim {e : ℕ} (z : Fin (e + 1) → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (he : ringKrullDim R = e + 1) :
    IsRegularLocalRing (R ⧸ Ideal.span {z 0}) ∧
      ringKrullDim (R ⧸ Ideal.span {z 0}) = e := by
  let : Nontrivial (R ⧸ Ideal.span {z 0}) :=
    Ideal.Quotient.nontrivial_iff.mpr (span_head_ne_top z hz)
  let : IsLocalRing (R ⧸ Ideal.span {z 0}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hgen := span_tail_quotient_eq_maximalIdeal z hz
  have hbound : (maximalIdeal (R ⧸ Ideal.span {z 0})).spanFinrank ≤ e := by
    rw [← hgen]
    exact spanFinrank_span_range_le _
  have hx : z 0 ∈ maximalIdeal R := hz ▸ Ideal.subset_span (Set.mem_range_self 0)
  have hlow := ringKrullDim_le_ringKrullDim_quotSMulTop_succ hx
  have hspan : z 0 • (⊤ : Ideal R) = Ideal.span {z 0} := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [hspan, he] at hlow
  have hlow' : (e : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {z 0}) :=
    ENat.WithBot.add_le_add_one_right_iff.mp hlow
  have hupper : ringKrullDim (R ⧸ Ideal.span {z 0}) ≤ (e : WithBot ℕ∞) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans (by exact_mod_cast hbound)
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_,
    le_antisymm hupper hlow'⟩
  have hbound' : ((maximalIdeal (R ⧸ Ideal.span {z 0})).spanFinrank : WithBot ℕ∞) ≤ e := by
    exact_mod_cast hbound
  exact hbound'.trans hlow'

end Quotient

section Parameters

open RingTheory.Sequence

/-- 全ての Noether 局所環について、次元と同数の極大イデアル生成元の先頭が正則なら、
その生成列は弱正則列である。長さに関する帰納法の接続を独立に述べる。 -/
theorem isWeaklyRegular_of_generator_regularity
    (hregular : ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
      {s : ℕ} (y : Fin (s + 1) → S),
      Ideal.span (Set.range y) = maximalIdeal S →
      ringKrullDim S = s + 1 → IsSMulRegular S (y 0))
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {e : ℕ} (z : Fin e → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (he : ringKrullDim R = e) : IsWeaklyRegular R (List.ofFn z) := by
  induction e generalizing R with
  | zero => simp
  | succ e ih =>
      have he' : ringKrullDim R = e + 1 := by simpa only [Nat.cast_succ] using he
      have hhead := hregular R z hz he'
      obtain ⟨hquotient, hdim⟩ :=
        isRegularLocalRing_quotient_head_and_dim z hz he'
      let : IsRegularLocalRing (R ⧸ Ideal.span {z 0}) := hquotient
      let q := Ideal.Quotient.mk (Ideal.span {z 0})
      have hgen : Ideal.span (Set.range (fun i : Fin e ↦ q (z i.succ))) =
          maximalIdeal (R ⧸ Ideal.span {z 0}) :=
        span_tail_quotient_eq_maximalIdeal z hz
      have htail : IsWeaklyRegular (R ⧸ Ideal.span {z 0})
          (List.ofFn (fun i : Fin e ↦ q (z i.succ))) :=
        ih _ _ hgen hdim
      have hmap : List.ofFn (fun i : Fin e ↦ q (z i.succ)) =
          (List.ofFn (Fin.tail z)).map (algebraMap R (R ⧸ Ideal.span {z 0})) := by
        rw [List.map_ofFn]
        rfl
      rw [hmap] at htail
      have htailR : IsWeaklyRegular (R ⧸ Ideal.span {z 0}) (List.ofFn (Fin.tail z)) :=
        (isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {z 0})
          (R ⧸ Ideal.span {z 0}) (List.ofFn (Fin.tail z))).mp htail
      let equiv : QuotSMulTop (z 0) R ≃ₗ[R] R ⧸ Ideal.span {z 0} :=
        Submodule.quotEquivOfEq _ _ (by
          rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
      rw [List.ofFn_succ]
      exact (isWeaklyRegular_cons_iff R (z 0) (List.ofFn (Fin.tail z))).mpr
        ⟨hhead, (equiv.isWeaklyRegular_congr (List.ofFn (Fin.tail z))).mpr htailR⟩

/-- 正則局所環 `A` で、`z = (z_1, …, z_e)` が `m_A` を生成し `e = dim A` なら、
`z` は弱正則列（各 `z_i` が `A/(z_1, …, z_{i-1})` の非零因子）。正則局所環の正則パラメータ系が
正則列であるという標準的な事実。 -/
theorem isWeaklyRegular_of_span_eq_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {e : ℕ} (z : Fin e → A) (hz : Ideal.span (Set.range z) = maximalIdeal A)
    (he : ringKrullDim A = e) : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z) := by
  apply isWeaklyRegular_of_generator_regularity ?_ A z hz he
  intro S _ _ _ s y hy hd
  exact HilbertSamuel.isSMulRegular_generator_of_span_eq_maximalIdeal S y hy hd 0

/-- 正則局所環の極大イデアルの最小生成列を選ぶ。
生成元の個数が Krull 次元に等しいことは Mathlib の定義から従う。
この列の正則性は、上の証明済み定理を適用して得る。 -/
lemma exists_regular_generators (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    ∃ rs : List R, RingTheory.Sequence.IsWeaklyRegular R rs ∧
      Ideal.ofList rs = maximalIdeal R ∧ ringKrullDim R = rs.length := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  let z : Fin s.toList.length → R := s.toList.get
  have hz : Ideal.span (Set.range z) = maximalIdeal R := by
    simpa [z] using hspan
  have hd : ringKrullDim R = s.toList.length := by
    simpa [hcard] using (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  refine ⟨s.toList, ?_, ?_, hd⟩
  · simpa only [z, List.ofFn_get] using isWeaklyRegular_of_span_eq_maximalIdeal R z hz hd
  · simpa [Ideal.ofList] using hspan

/-- Choose finitely indexed regular parameters, including the empty system in dimension zero. -/
lemma exists_regular_generators_fin (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    ∃ (n : ℕ) (z : Fin n → R),
      Ideal.span (Set.range z) = maximalIdeal R ∧
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z) ∧ ringKrullDim R = n := by
  obtain ⟨rs, hrs, hgen, hdim⟩ := exists_regular_generators R
  exact ⟨rs.length, rs.get, by simpa [Ideal.ofList] using hgen, by simpa using hrs, hdim⟩

end Parameters

/-- 正則局所環は整域である。極大イデアルの正則生成列を選び、
Noether 局所環に関する一般定理 `isDomain_of_regular_generators` を適用する。
正則パラメータの正則性も含めて証明済み。 -/
instance (priority := 100) isDomain_of_isRegularLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] : IsDomain A := by
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators A
  exact isDomain_of_regular_generators rs hreg hgen

end SerrePositivity
