module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseKanEnriched
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedComparisonIso

/-!
概要：対象の edgewise 解像と元の Kan 複体の族の大域的な coherent な比較。
方針：右端射影の豊穣自然性を二点図式で実現し、各成分の同値性から関手同型を得る。
規約：共通始域は Hom 自体も edgewise 解像した豊穣圏の coherent nerve。
使われ方：Kerodon §8.1.1、Corollary 5.6.0.6、左右の Hom の係数比較を一般の coherent な図式へ適用する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：対象の edgewise 解像の右端射影は全ての高次の Hom に関して自然な比較。
方針：共通の重みでの評価と右端射影の可換式を curry された作用へ移す。
規約：比較の各成分は実際の edgewiseRight。
使われ方：Kerodon §8.1.1、coherent な対象の比較の入力。 -/
def edgewiseKanRightComparison :
    KanEnrichedComparison edgewiseKanEnriched.{u} (edgewiseEnrichedRight KanObject.{u}) := by
  refine ⟨(fun X ↦ show edgewiseKanEnriched.obj X ⟶ X.val from edgewiseRight X.val.obj), ?_⟩
  intro X Y
  change (edgewiseRight X.val.obj ▷ edgewiseSubdivision ((ihom X.val.obj).obj Y.val.obj)) ≫
      uncurry (edgewiseRight ((ihom X.val.obj).obj Y.val.obj)) =
    uncurry (edgewiseKanEnrichedMap X.val.obj Y.val.obj) ≫ edgewiseRight Y.val.obj
  rw [edgewiseKanEnrichedMap, uncurry_curry]
  change (edgewiseRight X.val.obj ⊗ₘ edgewiseRight ((ihom X.val.obj).obj Y.val.obj)) ≫
      (ihom.ev X.val.obj).app Y.val.obj =
    edgewiseInternalHomEvaluation X.val.obj Y.val.obj ≫ edgewiseRight Y.val.obj
  exact (edgewiseInternalHomEvaluation_right X.val.obj Y.val.obj).symm

/-- 概要：対象の edgewise 解像の coherent な族。
方針：解像した Hom からの対象の豊穣作用に coherent nerve を適用する。
規約：始域は Hom を解像した Kan 複体の豊穣圏。
使われ方：Kerodon Corollary 5.6.0.6、元と反転した対象の共通の coherent な族。 -/
def edgewiseKanInfinityMap :
    SimplicialNerve (EdgewiseEnrichedObject KanObject.{u}) ⟶ SpaceInfinity.{u} :=
  coherentNerveMap edgewiseKanEnriched

/-- 概要：対象の edgewise 解像の族と元の対象の族は大域的に関手同型。
方針：豊穣な比較の実現に各右端射影の trivial Kan fibration 性を適用する。
規約：同型は対象ごとに選んだ同値の集まりではなく関手空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式への自然な置き換え。 -/
noncomputable def edgewiseKanInfinityComparisonIso :
    FunctorIso edgewiseKanInfinityMap.{u} (edgewiseEnrichedInfinityMap KanObject.{u}) :=
  kanEnrichedComparisonIso edgewiseKanRightComparison
    (fun X ↦ isQCatEquivalence_of_trivialKanFibration (edgewiseRight X.val.obj))

/-- 概要：対象の edgewise 解像の族も空間の coherent nerve と同値。
方針：元の対象への比較の同値の逆を使い、両合成の条件を大域的な比較の関手同型で移す。
規約：順方向は実際の対象の edgewise 解像の族。
使われ方：Kerodon Corollary 5.6.0.6、共通解像の対象側の同値データ。 -/
noncomputable def edgewiseKanInfinityEquivalence :
    QCatEquivalence (SimplicialNerve (EdgewiseEnrichedObject KanObject.{u})) SpaceInfinity.{u} where
  hom := edgewiseKanInfinityMap
  inv := (edgewiseEnrichedInfinityEquivalence KanObject.{u}).inv
  homInvIso := edgewiseKanInfinityComparisonIso.postcomp
      (edgewiseEnrichedInfinityEquivalence KanObject.{u}).inv ≪≫
    (edgewiseEnrichedInfinityEquivalence KanObject.{u}).homInvIso
  invHomIso := edgewiseKanInfinityComparisonIso.precomp
      (edgewiseEnrichedInfinityEquivalence KanObject.{u}).inv ≪≫
    (edgewiseEnrichedInfinityEquivalence KanObject.{u}).invHomIso

end SerrePositivity.InfinityCategories
