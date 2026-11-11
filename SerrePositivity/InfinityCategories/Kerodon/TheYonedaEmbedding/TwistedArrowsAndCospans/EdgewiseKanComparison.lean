module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseKanEnriched
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparisonIso

/-!
概要：対象の edgewise 解像と元の Kan 複体の族の大域的な coherent な比較。
方針：右端射影の豊穣自然性を二点図式で実現し、各成分の同値性から関手同型を得る。
規約：共通始域は Hom 自体も edgewise 解像した豊穣圏の coherent nerve。
使われ方：Kerodon §8.1.1（Tag 03JF）、Corollary 5.6.0.6（Tag 028T）、左右の Hom の係数比較を一般の coherent な図式へ適用する。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：対象の edgewise 解像の右端射影は全ての高次の Hom に関して自然な比較。
方針：共通の重みでの評価と右端射影の可換式を curry された作用へ移す。
規約：比較の各成分は実際の edgewiseRight。
使われ方：Kerodon §8.1.1（Tag 03JF）、coherent な対象の比較の入力。 -/
def edgewiseKanRightComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnriched.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedRight _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) := by
  refine ⟨(fun X ↦ show _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnriched.obj X ⟶ X.val from _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X.val.obj), ?_⟩
  intro X Y
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X.val.obj ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision ((ihom X.val.obj).obj Y.val.obj)) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight ((ihom X.val.obj).obj Y.val.obj)) =
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnrichedMap X.val.obj Y.val.obj) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight Y.val.obj
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnrichedMap, uncurry_curry]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X.val.obj ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight ((ihom X.val.obj).obj Y.val.obj)) ≫
      (ihom.ev X.val.obj).app Y.val.obj =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseInternalHomEvaluation X.val.obj Y.val.obj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight Y.val.obj
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseInternalHomEvaluation_right X.val.obj Y.val.obj).symm

/-- 概要：対象の edgewise 解像の coherent な族。
方針：解像した Hom からの対象の豊穣作用に coherent nerve を適用する。
規約：始域は Hom を解像した Kan 複体の豊穣圏。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元と反転した対象の共通の coherent な族。 -/
def edgewiseKanInfinityMap :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnriched

/-- 概要：対象の edgewise 解像の族と元の対象の族は大域的に関手同型。
方針：豊穣な比較の実現に各右端射影の trivial Kan fibration 性を適用する。
規約：同型は対象ごとに選んだ同値の集まりではなく関手空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な図式への自然な置き換え。 -/
noncomputable def edgewiseKanInfinityComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso edgewiseKanInfinityMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso edgewiseKanRightComparison
    (fun X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X.val.obj))

/-- 概要：対象の edgewise 解像の族も空間の coherent nerve と同値。
方針：元の対象への比較の同値の逆を使い、両合成の条件を大域的な比較の関手同型で移す。
規約：順方向は実際の対象の edgewise 解像の族。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共通解像の対象側の同値データ。 -/
noncomputable def edgewiseKanInfinityEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  hom := edgewiseKanInfinityMap
  inv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).inv
  homInvIso := edgewiseKanInfinityComparisonIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).inv ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).homInvIso
  invHomIso := edgewiseKanInfinityComparisonIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).inv ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).invHomIso

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
