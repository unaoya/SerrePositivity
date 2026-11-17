module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementRoofImage
public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedCommonRoofComparison
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementPinched

/-!
# 元の相対自由屋根と既存 CAlg_R の全 pinched 族の弱同値性

概要：同じ要素圏から構成した実屋根と実 pinched 族自身が弱同値である。
方針：元の正規化自由屋根への包含像で反映し、同じ局所化比較を合成する。
規約：元の全パラメータと実局所化源の両端を保持する。
使われ方：標準単位比較を検査する弱な probe の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Hammock _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：元の全相対屋根自身は弱同値。
方針：同じ全包含像と正規化自由屋根の弱同値性から包含を消去する。
規約：元の実写像を保持。使われ方：CAlg_R の全族の弱同値性。 -/
lemma freeProbeRelativeElementRoofMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeProbeRelativeElementRoofMap A X B) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (cofibrantAlgebraHammockColimitInclusionMap A (freeProbeElementCofibrantSource A X) B) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (reducedColimitIso _ _ _)).isWeakHomotopyEquivalence.comp
      (cofibrantAlgebraHammockInclusionMap_weak A _ _)
  apply hi.cancel_right
  rw [freeProbeRelativeElementRoofMap_image]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (freeProbeRelativeElementNormalizedIndexMap_localized_isIso A X B)).comp
      (freeNormalizedTensorReducedRoof_weak A X B.obj)

/-- 概要：既存 CAlg_R の元の全 pinched 族自身は弱同値。
方針：元の屋根・Ex∞ 単位・同じ二つの Hom 比較を合成する。
規約：元の全族と両頂点を保持。使われ方：標準単位比較の全族判定。 -/
lemma freeProbeRelativeElementPinchedMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeProbeRelativeElementPinchedMap A X B) := by
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
        (freeProbeRelativeElementSource A X) (ULiftHom.objUp.{u + 1, u + 1} B))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne _))
  exact (freeProbeRelativeElementRoofMap_weak A X B).comp
    (hu.comp ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap_weak _ _ _).comp
      (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationEquivalence (cofibrantAlgebraRelativeCategory A)).isFullyFaithful
        _ _).isQCatEquivalence.isWeakHomotopyEquivalence)))

end SerrePositivity.EInfinity.BarrattEccles
