module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOppositeKanEnriched
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EdgewiseCoherentDiagram

/-!
概要：元の対象の族と反転した対象の族の大域的な coherent な比較。
方針：対象の edgewise 解像からの左右の射影を豊穣な比較として実現し、関手同型を合成する。
規約：共通始域では Hom のパラメーター自体も edgewise 解像する。
使われ方：Kerodon §8.1.1（Tag 03JF）、Corollary 5.6.0.6（Tag 028T）、左右の Hom の係数を一般の coherent な図式で比較する。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：対象の edgewise 解像の左端射影は反転した対象への豊穣な比較。
方針：内部 Hom の反転した評価と左端射影の可換式を使う。
規約：各成分は実際の edgewiseLeft。
使われ方：Kerodon §8.1.1（Tag 03JF）、反転した係数を図式全体で比較する入力。 -/
def edgewiseKanLeftComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnriched.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnriched.{u} := by
  refine ⟨(fun X ↦ show _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnriched.obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnriched.obj X from
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X.val.obj), ?_⟩
  intro X Y
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X.val.obj ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision ((ihom X.val.obj).obj Y.val.obj)) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnrichedMap X.val.obj Y.val.obj) =
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnrichedMap X.val.obj Y.val.obj) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft Y.val.obj
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnrichedMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnrichedMap, uncurry_curry, uncurry_curry]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X.val.obj ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft ((ihom X.val.obj).obj Y.val.obj)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.oppositeInternalHomEvaluation X.val.obj Y.val.obj =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseInternalHomEvaluation X.val.obj Y.val.obj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft Y.val.obj
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseInternalHomEvaluation_left X.val.obj Y.val.obj).symm

/-- 概要：共通解像から反転した Kan 複体の coherent な族への写像。
方針：反転した対象の豊穣作用に coherent nerve を適用する。
規約：対象 X の像は X.val.obj.op を表す Kan 複体。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左 Hom の反転した係数に対応する族。 -/
def edgewiseOppositeKanInfinityMap :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnriched

/-- 概要：対象の共通解像と反転した対象の coherent な族は関手同型。
方針：左端射影の豊穣な比較を実現し、各成分の trivial Kan fibration 性を使う。
規約：対象ごとの同値の集まりではなく関手空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左 Hom の係数規約の大域的な比較。 -/
noncomputable def edgewiseOppositeKanInfinityComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanInfinityMap.{u} edgewiseOppositeKanInfinityMap.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso edgewiseKanLeftComparison
    (fun X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X.val.obj))

/-- 概要：元の対象の族と反転した対象の族は大域的に関手同型。
方針：共通の対象の edgewise 解像への右比較の逆と左比較を合成する。
規約：Hom の高次パラメーターを解像した共通始域上で述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左右の Hom の規約を同じ coherent な図式で接続する。 -/
noncomputable def edgewiseKanOppositeInfinityComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) edgewiseOppositeKanInfinityMap.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanInfinityComparisonIso.symm ≪≫ edgewiseOppositeKanInfinityComparisonIso

/-- 概要：反転した対象の coherent な族も空間の coherent nerve と同値。
方針：右端射影の比較の同値の逆を使い、大域的な関手同型で両合成の条件を移す。
規約：順方向は反転した対象の豊穣作用の coherent nerve。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な図式の左 Hom の係数への移送。 -/
noncomputable def edgewiseOppositeKanInfinityEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  hom := edgewiseOppositeKanInfinityMap
  inv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).inv
  homInvIso := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp edgewiseKanOppositeInfinityComparisonIso.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).inv ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).homInvIso
  invHomIso := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp edgewiseKanOppositeInfinityComparisonIso.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).inv ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).invHomIso

/-- 概要：一般の coherent な空間値図式の共通解像上で対象を反転した置き換え。
方針：Hom の共通解像に移した図式へ反転した対象の族を後合成する。
規約：値は選択した共通解像の対象の反転であり、元の値との厳密な等式は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左 Hom の係数を使う比較を一般の図式で行う。 -/
noncomputable def edgewiseCoherentOppositeReplacement {B : SSet.{u + 1}} (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.edgewiseCoherentDiagramLift F ≫ edgewiseOppositeKanInfinityMap

/-- 概要：一般の図式と共通解像上で対象を反転した図式は関手同型。
方針：共通解像から元への同型を戻し、元と反転した対象の大域的な比較を引き戻す。
規約：高次の自然性を持つ図式全体の同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左右の Hom の係数の比較の選択独立性。 -/
noncomputable def edgewiseCoherentOppositeReplacementIso {B : SSet.{u + 1}} (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (edgewiseCoherentOppositeReplacement F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.edgewiseCoherentDiagramLiftIso F).symm ≪≫
    edgewiseKanOppositeInfinityComparisonIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.edgewiseCoherentDiagramLift F)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
