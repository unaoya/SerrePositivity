module

public import SerrePositivity.KST.DerivedBlowup.KoszulBasis

/-!
概要：KST Def3.1 の Koszul 生成元の基底変換が関係式への微分と整合することを示す。
方針：次数−1の自由加群から係数環への線形写像を関係式から定義する。
規約：全 Koszul 複体の微分の構成とは区別し、その生成元上の制限を扱う。
使われ方：cdga の貼り合わせを外積代数へ延長する際の微分との可換性の入力。
-/

@[expose] public noncomputable section

universe v w

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I] {B : Type w} [CommRing B]

/-- 概要：チャートの Koszul 生成元上の微分。
方針：e_j を a_i x_j−a_j に送る線形写像を作る。
規約：KST Def3.1、x_i=1 を適用時に要求。使われ方：基底変換との可換性。 -/
def chartKoszulDifferential (a x : I → B) (i : I) : (ChartIndex i →₀ B) →ₗ[B] B :=
  Finsupp.linearCombination B (fun j : ChartIndex i => a i * x j.val - a j.val)

/-- 概要：微分の公式を省略された pivot にも延長する。
方針：pivot の関係式は0、他の生成元は自由加群の定義。
規約：KST §3.1、x_i=1。使われ方：Koszul 基底変換の全添字による計算。 -/
theorem chartKoszulDifferential_generator (a x : I → B) (i j : I) (hi : x i = 1) :
    chartKoszulDifferential a x i (koszulGenerator i j) = a i * x j - a j := by
  by_cases h : j = i
  · subst j
    simp [hi]
  · simp [koszulGenerator, h, chartKoszulDifferential]

omit [DecidableEq I] in
/-- 概要：規格化したチャートの関係式は基底変換された関係式に等しい。
方針：a_i x_k−a_k の項を引き単元律で整理する。
規約：KST Def3.1、環の可換性のみ。使われ方：Koszul 微分の自然性。 -/
theorem chartRelation_normalize (a x : I → B) (i k j : I) (s : Bˣ) (hs : ↑s = x k) :
    a k * normalizeCoordinates x s j - a j =
      (a i * x j - a j) - normalizeCoordinates x s j * (a i * x k - a k) := by
  rw [normalizeCoordinates, ← hs]
  calc
    _ = a i * x j - a j -
        (a i * x j * (↑s * ↑s⁻¹) - a k * (x j * ↑s⁻¹)) := by rw [s.mul_inv]; ring
    _ = _ := by ring

/-- 概要：Koszul 基底変換は次数−1から0への微分を保つ。
方針：生成元の変換と関係式の規格化公式を合わせ、自由加群全体に延長する。
規約：KST §3.1、非正則列も許す。使われ方：外積 cdga への延長の微分適合条件。 -/
theorem koszulGeneratorMap_differential (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    (chartKoszulDifferential a x i).comp (koszulGeneratorMap i k x s) =
      chartKoszulDifferential a (normalizeCoordinates x s) k := by
  have hg (j : I) :
      chartKoszulDifferential a x i (koszulGeneratorMap i k x s (koszulGenerator k j)) =
        chartKoszulDifferential a (normalizeCoordinates x s) k (koszulGenerator k j) := by
    rw [koszulGeneratorMap_generator i k j x s hs, map_sub, map_smul,
      chartKoszulDifferential_generator a x i j hi,
      chartKoszulDifferential_generator a x i k hi,
      chartKoszulDifferential_generator a (normalizeCoordinates x s) k j
        (normalizeCoordinates_pivot x k s hs)]
    exact (chartRelation_normalize a x i k j s hs).symm
  apply Finsupp.lhom_ext
  intro j c
  have hsingle : Finsupp.single j c = c • koszulGenerator k j.val := by simp
  change chartKoszulDifferential a x i (koszulGeneratorMap i k x s (Finsupp.single j c)) = _
  rw [hsingle, map_smul, map_smul, map_smul]
  exact congrArg (fun z => c • z) (hg j.val)

end SerrePositivity.KST.DerivedBlowup
