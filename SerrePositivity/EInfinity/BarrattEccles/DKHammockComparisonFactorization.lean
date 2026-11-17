module

public import SerrePositivity.EInfinity.BarrattEccles.DKHammockComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKHammockCoefficientComparison

/-!
# 元の代数 DK 比較と係数自然な比較の照合

概要：既存の代数の高次比較は係数自然な一般比較と同じ包含の合成である。
方針：同じ元の右弱比較を消去し、左射の定義を照合する。
規約：既存の比較同型を新しい選択に置き換えない。
使われ方：既存 Map^h の比較への係数自然性の移送。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]
  (X Y : (cofibrantAlgebraRelativeCategory A).category)

lemma cofibrantAlgebraDKHammockComparisonIso_factorization :
    (cofibrantAlgebraDKHammockComparisonIso A X Y).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso (cofibrantAlgebraRelativeCategory A) X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (cofibrantAlgebraHammockInclusionMap A X Y) := by
  have := Hammock.anodyneQ_map_isIso_of_weak
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison (cofibrantAlgebraRelativeCategory A) X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence
      (cofibrantAlgebraRelativeCategory A) X Y)
  apply (cancel_epi (AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison (cofibrantAlgebraRelativeCategory A) X Y))).mp
  rw [cofibrantAlgebraDKHammockComparisonIso_fac, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_fac, ← Functor.map_comp]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
