module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeInvertP
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# 分冪生成と p 反転後の比較

## 概要
有理代数の比較で分冪の生成元が持ち上がれば、生成される部分代数全体が像に入る。
その部分代数が稠密で連続な分裂があれば全射となる。

## 方針
階乗の逆数による分冪の式を使い、部分代数の生成の普遍性を適用する。

## 規約
BS 著者版 Example 7.9 の G-A3-7 の古典的な部分。

## 使われ方
Banach 代数の次数一の分冪生成と包絡の比較。
-/

public section

namespace SerrePositivity.BhattScholze

/-- 概要：比較の像に入る元の分冪で生成した有理部分代数は、比較の像に含まれる。
方針：各分冪を階乗で割った冪として持ち上げ、生成された部分代数の普遍性を使う。
規約：G-A3-7 の p 反転後の分冪計算。
使われ方：一次の生成元から全ての有限な式を持ち上げる。 -/
theorem adjoin_dividedPowers_le_range
    {B C S : Type*} [CommRing B] [CommRing C] [Algebra ℚ B] [Algebra ℚ C]
    (q : B →ₐ[ℚ] C) {J : Ideal C} (H : DividedPowers J) (s : S → C)
    (hs : ∀ i, s i ∈ J) (hqs : ∀ i, s i ∈ Set.range q) :
    Algebra.adjoin ℚ (Set.range fun z : S × ℕ => H.dpow z.2 (s z.1)) ≤ q.range := by
  apply Algebra.adjoin_le
  rintro _ ⟨⟨i, n⟩, rfl⟩
  exact dividedPower_mem_range_of_ratAlgHom q H (hs i) (hqs i) n

/-- 概要：分冪生成される稠密な部分代数が比較の像に入り、連続な分裂があれば全射。
方針：分冪生成した部分代数の稠密性を比較の像へ移し、像の閉性を適用する。
規約：BS 著者版 Example 7.9 の G-A3-7 の古典的な判定。
使われ方：p 反転後の比較の全射性。 -/
theorem surjective_of_dense_dividedPower_generators_retraction
    {B C S : Type*} [CommRing B] [CommRing C] [Algebra ℚ B] [Algebra ℚ C]
    [TopologicalSpace B] [TopologicalSpace C] [T2Space C]
    (q : B →ₐ[ℚ] C) (r : C → B) (hq : Continuous q) (hr : Continuous r)
    (h : Function.LeftInverse r q) {J : Ideal C} (H : DividedPowers J) (s : S → C)
    (hs : ∀ i, s i ∈ J) (hqs : ∀ i, s i ∈ Set.range q)
    (hd : Dense (Algebra.adjoin ℚ (Set.range fun z : S × ℕ => H.dpow z.2 (s z.1)) : Set C)) :
    Function.Surjective q := by
  apply surjective_of_continuous_retraction_of_denseRange q r hq hr h
  exact hd.mono (adjoin_dividedPowers_le_range q H s hs hqs)

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 7.9" (partial := component) "BS-W15 K5（11-11）：envelope の側は本体（R の有界性を仮定する原典の形、D76。結論は有界な prism）。p 反転の議論 G-A3-7 の古典的な入力（余法加群、分冪の像の稠密性）も本体。Δ_R/A との同一視と HT 比較の適用は drafts の A3/LciAndQuasiregular"] _root_.SerrePositivity.BhattScholze.surjective_of_dense_dividedPower_generators_retraction
