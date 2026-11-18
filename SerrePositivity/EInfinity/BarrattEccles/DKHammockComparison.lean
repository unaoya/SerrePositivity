module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockInclusionLaws
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagonalReductionWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagonalComparisonWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakAnodyneLocalization

/-!
# 実 DK Hom と元の全代数の hammock の高次比較

概要：元の自由 hammock 対角の同じ二射を通じて実 DK Hom のホモトピー型を比較する。
方針：元の cofibrant 包含を左射に合成し、同じ弱同値を anodyne 局所化で反転する。
規約：π₀ だけの比較に置き換えず、元の全単体と同じ比較射を使う。
使われ方：既存 Map^h との高次比較の共通標的。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]
  (X Y : (cofibrantAlgebraRelativeCategory A).category)
def cofibrantAlgebraDiagonalHammockMap :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonal (cofibrantAlgebraRelativeCategory A) X Y ⟶
      algebraReducedHammock A ((cofibrantAlgebraDKInclusion A).obj X)
        ((cofibrantAlgebraDKInclusion A).obj Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction (cofibrantAlgebraRelativeCategory A) X Y ≫
    cofibrantAlgebraHammockInclusionMap A X Y
lemma cofibrantAlgebraDiagonalHammockMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantAlgebraDiagonalHammockMap A X Y) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction_isWeakHomotopyEquivalence
    (cofibrantAlgebraRelativeCategory A) X Y).comp (cofibrantAlgebraHammockInclusionMap_weak A X Y)
def cofibrantAlgebraDKHammockComparisonIso :
    AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom (cofibrantAlgebraRelativeCategory A) X Y) ≅
      AnodyneHomotopy.anodyneQ.obj
        (algebraReducedHammock A ((cofibrantAlgebraDKInclusion A).obj X)
          ((cofibrantAlgebraDKInclusion A).obj Y)) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison (cofibrantAlgebraRelativeCategory A) X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence
      (cofibrantAlgebraRelativeCategory A) X Y)
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak (cofibrantAlgebraDiagonalHammockMap A X Y)
    (cofibrantAlgebraDiagonalHammockMap_weak A X Y)
  exact (asIso (AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison (cofibrantAlgebraRelativeCategory A) X Y))).symm ≪≫
      asIso (AnodyneHomotopy.anodyneQ.map (cofibrantAlgebraDiagonalHammockMap A X Y))
lemma cofibrantAlgebraDKHammockComparisonIso_fac :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison (cofibrantAlgebraRelativeCategory A) X Y) ≫
      (cofibrantAlgebraDKHammockComparisonIso A X Y).hom =
    AnodyneHomotopy.anodyneQ.map (cofibrantAlgebraDiagonalHammockMap A X Y) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison (cofibrantAlgebraRelativeCategory A) X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence
      (cofibrantAlgebraRelativeCategory A) X Y)
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _
end SerrePositivity.EInfinity.BarrattEccles
