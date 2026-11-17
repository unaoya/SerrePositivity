module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraReplacement
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativeLocalization

/-!
# Cofibrant E 代数と元の全代数の普通の局所化の比較

概要：Dwyer–Kan の準備として、同じ包含と置換による局所化の同値を構成する。
方針：元の二つの自然な弱同値比較を普通の局所化へ送る。
規約：単体的局所化の普遍性や高次の合成は別に構成する。
使われ方：E2b の単体的局所化と既存の局所化 Hom の比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra

variable (A : Type u) [CommRing A]

/-- 概要：cofibrant E 代数の局所化は元の代数の局所化と同値（Dwyer–Kan）。
方針：元の包含・関手的置換と両側の比較の弱同値性を使う。
規約：逆関手も指定済みの具体的な置換から作る。
使われ方：E2b の同じ対象からの普通のホモトピー圏比較。 -/
def cofibrantAlgebraHoEquivalence :
    let := modelCategory A
    (cofibrantAlgebraWeakEquivalences A).Localization ≌
      (weakEquivalences (operad A).Algebra).Localization := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeLocalization.equivalence
    (cofibrantAlgebraInclusionRelative A) (cofibrantAlgebraReplacementRelative A)
    (cofibrantAlgebraRestrictedComparison A) (cofibrantAlgebraReplacementComparison A)
    (cofibrantAlgebraRestrictedComparison_weakEquivalence A)
    (cofibrantAlgebraReplacementComparison_weakEquivalence A)

/-- 概要：包含と局所化同値の同じ因子化自然同型（Dwyer–Kan）。
方針：元の包含の局所化 lift の同じ比較を使う。
規約：元の対象の局所化像で評価する。
使われ方：Map^h の π₀ 比較の成分の追跡。 -/
def cofibrantAlgebraInclusionLocalizedIso :
    let := modelCategory A
    cofibrantAlgebraInclusion A ⋙ (weakEquivalences (operad A).Algebra).Q ≅
      (cofibrantAlgebraWeakEquivalences A).Q ⋙ (cofibrantAlgebraHoEquivalence A).functor := by
  let := modelCategory A
  change (cofibrantAlgebraInclusionRelative A).functor ⋙
    (weakEquivalences (operad A).Algebra).Q ≅ (cofibrantAlgebraWeakEquivalences A).Q ⋙
      ((cofibrantAlgebraInclusionRelative A).localizedFunctor
        (cofibrantAlgebraWeakEquivalences A).Q (weakEquivalences (operad A).Algebra).Q)
  exact CatCommSq.iso _ _ _ _

/-- 概要：包含は普通の局所化上の同値を誘導（Dwyer–Kan）。
方針：同じ順関手を持つ構成済みの同値の保証を使う。
規約：元の具体的なモデル構造を局所的に選ぶ。
使われ方：通常の局所化の包含比較 API。 -/
lemma cofibrantAlgebraInclusion_isLocalizedEquivalence :
    let := modelCategory A
    (cofibrantAlgebraInclusionRelative A).IsLocalizedEquivalence := by
  let := modelCategory A
  exact ⟨(cofibrantAlgebraHoEquivalence A).isEquivalence_functor⟩

/-- 概要：元の代数局所化への包含後の関手も同じ弱同値の局所化（Hovey §1.2）。
方針：包含の局所化同値性と元の普通の局所化を合成する。
規約：元の代数局所化の対象・射をそのまま使う。
使われ方：cofibrant 対象の Map^h と元の局所化 Hom の照合。 -/
lemma cofibrantAlgebraInclusion_isLocalization :
    let := modelCategory A
    (cofibrantAlgebraInclusion A ⋙ (weakEquivalences (operad A).Algebra).Q).IsLocalization
      (cofibrantAlgebraWeakEquivalences A) := by
  let := modelCategory A
  have := cofibrantAlgebraInclusion_isLocalizedEquivalence A
  change ((cofibrantAlgebraInclusionRelative A).functor ⋙
    (weakEquivalences (operad A).Algebra).Q).IsLocalization _
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
