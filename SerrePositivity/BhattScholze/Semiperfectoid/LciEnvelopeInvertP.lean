module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.RingTheory.DividedPowers.RatAlgebra
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# p を反転した比較の全射性

## 概要
連続な分裂と、フィルトレーションに沿う稠密性から、比較写像の全射性を得る。

## 方針
分裂した像を連続な自己写像の固定点集合として閉じる。フィルトレーションでは各段を帰納して像に入れる。

## 規約
BS 著者版 Example 7.9 の G-A3-7 の古典的な部分。位相は比較先に与える。

## 使われ方
普遍的な包絡の p を反転した後の比較。
-/

public section

namespace SerrePositivity.BhattScholze

/-- 概要：連続な左逆を持つ比較の稠密な像は Hausdorff 空間全体。
方針：比較と左逆の合成の固定点集合は閉集合なので、像の閉包に等しい。
規約：p 反転後に与えられた位相で使う G-A3-7 の閉像の議論。
使われ方：包絡の比較の全射性。 -/
theorem surjective_of_continuous_retraction_of_denseRange
    {B C : Type*} [TopologicalSpace B] [TopologicalSpace C] [T2Space C]
    (q : B → C) (r : C → B) (hq : Continuous q) (hr : Continuous r)
    (h : Function.LeftInverse r q) (hd : DenseRange q) :
    Function.Surjective q := by
  have hclosed : IsClosed {c : C | q (r c) = c} :=
    isClosed_eq (hq.comp hr) continuous_id
  intro c
  have hc : c ∈ {c : C | q (r c) = c} :=
    (closure_minimal (by rintro _ ⟨b, rfl⟩; exact congrArg q (h b)) hclosed) (hd c)
  exact ⟨r c, hc⟩

/-- 概要：初項と各段の剰余を持ち上げられる加法群の射は、フィルトレーションの各段を像に含む。
方針：各剰余の代表元を引いた差に帰納法を適用する。
規約：G-A3-7 の稠密性に用いる有限段の持ち上げ。
使われ方：分冪の次数ごとの生成から像の稠密性を得る。 -/
theorem filtration_le_range_of_lift {B C : Type*} [AddGroup B] [AddGroup C]
    (q : B →+ C) (F : ℕ → AddSubgroup C) (h₀ : F 0 ≤ q.range)
    (hs : ∀ n x, x ∈ F (n + 1) → ∃ b, -q b + x ∈ F n) :
    ∀ n, F n ≤ q.range := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    intro x hx
    obtain ⟨b, hb⟩ := hs n x hx
    obtain ⟨c, hc⟩ := ih hb
    exact ⟨b + c, by rw [map_add, hc, ← add_assoc, add_neg_cancel, zero_add]⟩

/-- 概要：有理代数の比較の像は、像に属する元の分冪を含む。
方針：分冪を階乗の逆数のスカラー倍で表し、比較の元を同じ式で取る。
規約：G-A3-7 の p 反転後の古典的な分冪計算。
使われ方：次数一の持ち上げから高い次数の分冪を持ち上げる。 -/
theorem dividedPower_mem_range_of_ratAlgHom
    {B C : Type*} [CommRing B] [CommRing C] [Algebra ℚ B] [Algebra ℚ C]
    (q : B →ₐ[ℚ] C) {J : Ideal C} (H : DividedPowers J)
    {x : C} (hx : x ∈ J) (hqx : x ∈ Set.range q) (n : ℕ) :
    H.dpow n x ∈ Set.range q := by
  obtain ⟨b, rfl⟩ := hqx
  rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul J H hx]
  exact ⟨_ • b ^ n, by rw [map_smul, map_pow]⟩

/-- 概要：差商の比較先の類が余法加群を生成するための判定。
方針：関係の生成元の剰余での像を、余法加群の全射に沿って移す。
規約：G-A3-7 の `[z_i] = f̄_i mod J̄²` が得られた後の計算。
使われ方：フィルトレーションの一次の生成。 -/
theorem cotangent_span_eq_top_of_relation_classes
    {R σ : Type*} [CommRing R] {J : Ideal R} (f : σ → R)
    (hJ : Ideal.span (Set.range f) = J) (z : σ → J.Cotangent)
    (hz : ∀ i, z i = J.toCotangent ⟨f i, hJ ▸ Ideal.subset_span ⟨i, rfl⟩⟩) :
    Submodule.span R (Set.range z) = ⊤ := by
  have hf (i : σ) : f i ∈ J := hJ ▸ Ideal.subset_span ⟨i, rfl⟩
  let g : σ → J := fun i => ⟨f i, hf i⟩
  have hg : Submodule.span R (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective J.subtype_injective
    rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top, Submodule.range_subtype]
    exact hJ
  have hzg : Set.range z = J.toCotangent '' Set.range g := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext hz)
  rw [hzg, ← Submodule.map_span, hg, Submodule.map_top, J.toCotangent_range]

/-- 概要：有限段での持ち上げと稠密な和から、連続な分裂比較の全射性を得る。
方針：各段を像に入れ、その合併の稠密性を像へ移す。
規約：BS 著者版 Example 7.9、G-A3-7 の古典的な全射性の判定。
使われ方：p を反転した包絡の比較。 -/
theorem surjective_of_dense_filtration_retraction
    {B C : Type*} [AddGroup B] [AddGroup C]
    [TopologicalSpace B] [TopologicalSpace C] [T2Space C]
    (q : B →+ C) (r : C → B) (hq : Continuous q) (hr : Continuous r)
    (h : Function.LeftInverse r q) (F : ℕ → AddSubgroup C) (h₀ : F 0 ≤ q.range)
    (hs : ∀ n x, x ∈ F (n + 1) → ∃ b, -q b + x ∈ F n)
    (hd : Dense (⋃ n, (F n : Set C))) : Function.Surjective q := by
  apply surjective_of_continuous_retraction_of_denseRange q r hq hr h
  exact hd.mono (Set.iUnion_subset fun n => filtration_le_range_of_lift q F h₀ hs n)

end SerrePositivity.BhattScholze
