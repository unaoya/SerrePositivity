module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeKanEnriched
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseCoherentDiagram

/-!
概要：元の対象の族と反転した対象の族の大域的な coherent な比較。
方針：対象の edgewise 解像からの左右の射影を豊穣な比較として実現し、関手同型を合成する。
規約：共通始域では Hom のパラメーター自体も edgewise 解像する。
使われ方：Kerodon §8.1.1、Corollary 5.6.0.6、左右の Hom の係数を一般の coherent な図式で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：対象の edgewise 解像の左端射影は反転した対象への豊穣な比較。
方針：内部 Hom の反転した評価と左端射影の可換式を使う。
規約：各成分は実際の edgewiseLeft。
使われ方：Kerodon §8.1.1、反転した係数を図式全体で比較する入力。 -/
def edgewiseKanLeftComparison :
    KanEnrichedComparison edgewiseKanEnriched.{u} edgewiseOppositeKanEnriched.{u} := by
  refine ⟨(fun X ↦ show edgewiseKanEnriched.obj X ⟶ edgewiseOppositeKanEnriched.obj X from
    edgewiseLeft X.val.obj), ?_⟩
  intro X Y
  change (edgewiseLeft X.val.obj ▷ edgewiseSubdivision ((ihom X.val.obj).obj Y.val.obj)) ≫
      uncurry (edgewiseOppositeKanEnrichedMap X.val.obj Y.val.obj) =
    uncurry (edgewiseKanEnrichedMap X.val.obj Y.val.obj) ≫ edgewiseLeft Y.val.obj
  rw [edgewiseOppositeKanEnrichedMap, edgewiseKanEnrichedMap, uncurry_curry, uncurry_curry]
  change (edgewiseLeft X.val.obj ⊗ₘ edgewiseLeft ((ihom X.val.obj).obj Y.val.obj)) ≫
      oppositeInternalHomEvaluation X.val.obj Y.val.obj =
    edgewiseInternalHomEvaluation X.val.obj Y.val.obj ≫ edgewiseLeft Y.val.obj
  exact (edgewiseInternalHomEvaluation_left X.val.obj Y.val.obj).symm

/-- 概要：共通解像から反転した Kan 複体の coherent な族への写像。
方針：反転した対象の豊穣作用に coherent nerve を適用する。
規約：対象 X の像は X.val.obj.op を表す Kan 複体。
使われ方：Kerodon Corollary 5.6.0.6、左 Hom の反転した係数に対応する族。 -/
def edgewiseOppositeKanInfinityMap :
    SimplicialNerve (EdgewiseEnrichedObject KanObject.{u}) ⟶ SpaceInfinity.{u} :=
  coherentNerveMap edgewiseOppositeKanEnriched

/-- 概要：対象の共通解像と反転した対象の coherent な族は関手同型。
方針：左端射影の豊穣な比較を実現し、各成分の trivial Kan fibration 性を使う。
規約：対象ごとの同値の集まりではなく関手空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6、左 Hom の係数規約の大域的な比較。 -/
noncomputable def edgewiseOppositeKanInfinityComparisonIso :
    FunctorIso edgewiseKanInfinityMap.{u} edgewiseOppositeKanInfinityMap.{u} :=
  kanEnrichedComparisonIso edgewiseKanLeftComparison
    (fun X ↦ isQCatEquivalence_of_trivialKanFibration (edgewiseLeft X.val.obj))

/-- 概要：元の対象の族と反転した対象の族は大域的に関手同型。
方針：共通の対象の edgewise 解像への右比較の逆と左比較を合成する。
規約：Hom の高次パラメーターを解像した共通始域上で述べる。
使われ方：Kerodon Corollary 5.6.0.6、左右の Hom の規約を同じ coherent な図式で接続する。 -/
noncomputable def edgewiseKanOppositeInfinityComparisonIso :
    FunctorIso (edgewiseEnrichedInfinityMap KanObject.{u}) edgewiseOppositeKanInfinityMap.{u} :=
  edgewiseKanInfinityComparisonIso.symm ≪≫ edgewiseOppositeKanInfinityComparisonIso

/-- 概要：反転した対象の coherent な族も空間の coherent nerve と同値。
方針：右端射影の比較の同値の逆を使い、大域的な関手同型で両合成の条件を移す。
規約：順方向は反転した対象の豊穣作用の coherent nerve。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式の左 Hom の係数への移送。 -/
noncomputable def edgewiseOppositeKanInfinityEquivalence :
    QCatEquivalence (SimplicialNerve (EdgewiseEnrichedObject KanObject.{u})) SpaceInfinity.{u} where
  hom := edgewiseOppositeKanInfinityMap
  inv := (edgewiseEnrichedInfinityEquivalence KanObject.{u}).inv
  homInvIso := FunctorIso.postcomp edgewiseKanOppositeInfinityComparisonIso.symm
      (edgewiseEnrichedInfinityEquivalence KanObject.{u}).inv ≪≫
    (edgewiseEnrichedInfinityEquivalence KanObject.{u}).homInvIso
  invHomIso := FunctorIso.precomp edgewiseKanOppositeInfinityComparisonIso.symm
      (edgewiseEnrichedInfinityEquivalence KanObject.{u}).inv ≪≫
    (edgewiseEnrichedInfinityEquivalence KanObject.{u}).invHomIso

/-- 概要：一般の coherent な空間値図式の共通解像上で対象を反転した置き換え。
方針：Hom の共通解像に移した図式へ反転した対象の族を後合成する。
規約：値は選択した共通解像の対象の反転であり、元の値との厳密な等式は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、左 Hom の係数を使う比較を一般の図式で行う。 -/
noncomputable def edgewiseCoherentOppositeReplacement {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    B ⟶ SpaceInfinity.{u} := edgewiseCoherentDiagramLift F ≫ edgewiseOppositeKanInfinityMap

/-- 概要：一般の図式と共通解像上で対象を反転した図式は関手同型。
方針：共通解像から元への同型を戻し、元と反転した対象の大域的な比較を引き戻す。
規約：高次の自然性を持つ図式全体の同型。
使われ方：Kerodon Corollary 5.6.0.6、左右の Hom の係数の比較の選択独立性。 -/
noncomputable def edgewiseCoherentOppositeReplacementIso {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    FunctorIso F (edgewiseCoherentOppositeReplacement F) :=
  (edgewiseCoherentDiagramLiftIso F).symm ≪≫
    edgewiseKanOppositeInfinityComparisonIso.precomp (edgewiseCoherentDiagramLift F)

end SerrePositivity.InfinityCategories
