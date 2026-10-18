module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalTransitionBasis

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子遷移と blowup チャート遷移の整合性。
方針：Cartier 生成元を含まない部分を全生成加群へ埋め、共通 Koszul 表示への変換で比較する。
規約：規格化座標を同じ重なり係数環で計算する。係数環移送は別段階。
使われ方：例外因子の局所比較を大域の閉埋め込みへ接続する基底変換。
-/

@[expose] public noncomputable section

universe v w

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I] {B : Type w} [CommRing B]

/-- 概要：チャートの生成元を例外因子の全生成加群へ含める。
方針：pivot 以外の標準基底を同じ添字の標準基底へ送る。
規約：KST Lemma 3.6。使われ方：局所閉埋め込みの Koszul 射。 -/
def exceptionalChartGeneratorInclusion (i : I) : (ChartIndex i →₀ B) →ₗ[B] (I →₀ B) :=
  Finsupp.linearCombination B (fun j : ChartIndex i => Finsupp.single j.val 1)

/-- 概要：局所閉埋め込みと共通表示への変換の生成元公式。
方針：pivot の場合は零、他は標準基底の変換を計算する。
規約：KST Lemma 3.6、x_i=1。使われ方：チャートと例外因子の遷移の比較。 -/
theorem exceptionalGeneratorMap_chartInclusion (i j : I) (x : I → B) (hi : x i = 1) :
    exceptionalGeneratorMap i x
        (exceptionalChartGeneratorInclusion (B := B) i (koszulGenerator i j)) =
      x j • Finsupp.single i 1 - Finsupp.single j 1 := by
  by_cases hj : j = i
  · subst j
    simp [hi]
  · simp [koszulGenerator, hj, exceptionalChartGeneratorInclusion,
      exceptionalGeneratorMap_single]

/-- 概要：例外因子の遷移は blowup チャートの指定基底変換を延長する。
方針：共通表示への可逆基底変換で比較し、規格化座標の単元律で余分な項を消す。
規約：KST Def 3.1・Lemma 3.6、s=x_k、x_i=1。
使われ方：j の局所 Koszul 射の重なりでの可換性。 -/
theorem exceptionalTransitionEquiv_chart_generator (i k j : I) (x : I → B) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    exceptionalTransitionEquiv i k x (normalizeCoordinates x s)
        (exceptionalChartGeneratorInclusion (B := B) k (koszulGenerator k j)) =
      exceptionalChartGeneratorInclusion (B := B) i
        (koszulGeneratorMap i k x s (koszulGenerator k j)) := by
  apply (exceptionalGeneratorEquiv i x).injective
  change exceptionalGeneratorMap i x
      (exceptionalTransitionEquiv i k x (normalizeCoordinates x s)
        (exceptionalChartGeneratorInclusion k (koszulGenerator k j))) =
    exceptionalGeneratorMap i x
      (exceptionalChartGeneratorInclusion i
        (koszulGeneratorMap i k x s (koszulGenerator k j)))
  rw [exceptionalTransitionEquiv_comparison,
    exceptionalGeneratorMap_chartInclusion k j (normalizeCoordinates x s)
      (normalizeCoordinates_pivot x k s hs),
    koszulGeneratorMap_generator i k j x s hs, map_sub, map_smul, map_sub, map_smul,
    exceptionalGeneratorMap_chartInclusion i j x hi,
    exceptionalGeneratorMap_chartInclusion i k x hi]
  have hc : normalizeCoordinates x s j * x k = x j := by
    rw [normalizeCoordinates, ← hs, mul_assoc, s.inv_mul, mul_one]
  rw [smul_sub, smul_smul, hc]
  abel

/-- 概要：例外因子の遷移とチャート生成加群の包含は可換。
方針：指定生成元の可換式を自由加群の普遍性で線形に延長する。
規約：KST Def 3.1・Lemma 3.6。使われ方：外積 dg 射の可換式への入力。 -/
theorem exceptionalTransitionEquiv_chart (i k : I) (x : I → B) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    (exceptionalTransitionEquiv i k x (normalizeCoordinates x s)).toLinearMap.comp
        (exceptionalChartGeneratorInclusion k) =
      (exceptionalChartGeneratorInclusion i).comp (koszulGeneratorMap i k x s) := by
  apply Finsupp.lhom_ext
  intro j c
  have he : Finsupp.single j c = c • koszulGenerator (B := B) k j.val := by simp
  change exceptionalTransitionEquiv i k x (normalizeCoordinates x s)
      (exceptionalChartGeneratorInclusion k (Finsupp.single j c)) =
    exceptionalChartGeneratorInclusion i
      (koszulGeneratorMap i k x s (Finsupp.single j c))
  rw [he, map_smul, map_smul, map_smul, map_smul,
    exceptionalTransitionEquiv_chart_generator i k j.val x s hi hs]

end SerrePositivity.KST.DerivedBlowup
