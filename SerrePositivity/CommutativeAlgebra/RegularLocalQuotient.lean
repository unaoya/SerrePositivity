module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Card

/-! # 最小生成元の先頭による正則局所環の商

次元と同数の元が極大イデアルを生成するとき、先頭で割った商は再び正則局所環で、
次元が一つ下がる。Krull 次元の下界と残りの生成元の個数の上界だけを用いる。
正則列・整域性の未証明入力は使わない。
-/

@[expose] public section

open IsLocalRing
open scoped Pointwise

namespace SerrePositivity.RegularLocalQuotient

variable {R : Type*} [CommRing R]

/-- 有限族が生成するイデアルの最小生成数は、族の長さ以下である。 -/
theorem spanFinrank_span_range_le {e : ℕ} (z : Fin e → R) :
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

/-- 次元と同数の極大イデアル生成元の先頭は非零である。 -/
theorem head_ne_zero {e : ℕ} (z : Fin (e + 1) → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (he : ringKrullDim R = e + 1) : z 0 ≠ 0 := by
  intro hzero
  have hdim := (isRegularLocalRing_quotient_head_and_dim z hz he).2
  rw [hzero, Ideal.span_singleton_zero] at hdim
  have hR : ringKrullDim R = e :=
    (RingEquiv.ringKrullDim (RingEquiv.quotientBot R)).symm.trans hdim
  have hbad : e + 1 = e := by exact_mod_cast he.symm.trans hR
  omega

end SerrePositivity.RegularLocalQuotient
