module
public import SerrePositivity.KST.SConstruction.CoherentIntervalFamilyRecovery
public import SerrePositivity.KST.SConstruction.LoopCollageEvaluation

/-! # Loop collage の区間族から元の suspension 写像族への相対回収
概要：局所 Kan な collage の固定端点の族を、元の suspension の写像空間へ戻す。
方針：元の suspension–loop 同型を固定端点比較へ合成し、境界固定の回収を適用する。
規約：全点つき単体集合の nerve の Kan 性を仮定せず、collage の局所 Kan 性を使う。
使われ方：元の K 構造射の全パラメータの円柱を、境界付きの native な族へ変換する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra SerrePositivity.InfinityCategories

/-- 元の suspension 写像空間から、collage 内の下段・上段間の区間模型への比較。 -/
def loopCollageSuspensionIntervalComparison (X Y : PointedKanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj) Y.obj).right ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((enrichedFunctorCollageBottom
          pointedKanLoopEnrichedFunctor).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((enrichedFunctorCollageTop
          pointedKanLoopEnrichedFunctor).obj Y)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (suspensionLoopMappingIso X.obj Y.obj).hom ≫
    coherentMappingIntervalComparison
      ((enrichedFunctorCollageBottom pointedKanLoopEnrichedFunctor).obj X)
      ((enrichedFunctorCollageTop pointedKanLoopEnrichedFunctor).obj Y)

/-- 元の随伴同型と局所 Kan な collage の比較から、同じ suspension 比較が同値。 -/
lemma loopCollageSuspensionIntervalComparison_isQCatEquivalence
    (X Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (loopCollageSuspensionIntervalComparison X Y) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso
    (suspensionLoopMappingIso X.obj Y.obj))).isQCatEquivalence.comp
      (coherentMappingIntervalComparison_isQCatEquivalence _ _)

/-- 指定した元の suspension 写像族を境界に保ち、比較円柱も境界で固定する回収。 -/
def relativeLoopCollageSuspensionFamilyRecovery (X Y : PointedKanObject.{u})
    {T U : SSet.{u + 1}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj) Y.obj).right)
    (b : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((enrichedFunctorCollageBottom
        pointedKanLoopEnrichedFunctor).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((enrichedFunctorCollageTop
        pointedKanLoopEnrichedFunctor).obj Y)))
    (h : a ≫ loopCollageSuspensionIntervalComparison X Y = j ≫ b) :
    RelativeEquivalenceFamilyData (loopCollageSuspensionIntervalComparison X Y) j a b :=
  relativeEquivalenceFamilyRecovery _
    (loopCollageSuspensionIntervalComparison_isQCatEquivalence X Y) j a b h

end SerrePositivity.KST.SConstruction
