module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanOppositeCoefficients
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFunctor

/-!
概要：元の Kan 値図式の weighted nerve と、値を反転した coherent 図式の unstraightening の比較。
方針：一点からの Hom の二重反転による自然同型を weighted nerve に写し、既存の比較へ合成する。
規約：底の圏は固定し、図式の値に一度だけ反転を施した coherent 表示を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の weighted nerve から coherent な復元への接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：反転した図式の一点からの反転係数の weighted nerve は元の係数の weighted nerve と同型。
方針：係数の自然同型を weighted nerve の通常の関手に写し、底上の同型から全空間の同型を得る。
規約：底を厳密に保つ同型を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の図式の係数による復元比較。 -/
noncomputable def oppositePointHomWeightedIso
    {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
      (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject ⋙ SSet.opFunctor) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  (Over.forget (nerve C)).mapIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFunctor C).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.oppositePointHomDiagramIso F))

/-- 概要：係数の weighted nerve 同型の逆射は元の底への射影を保つ。
方針：Over 圏での同型の逆射の可換性を取り出す。
規約：逆射は元の係数から豊穣係数への比較に使う向き。
使われ方：Kerodon §5.6.2（Tag 026H）、復元比較の底上の可換性。 -/
lemma oppositePointHomWeightedIso_inv_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (oppositePointHomWeightedIso F).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
        (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject ⋙ SSet.opFunctor) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFunctor C).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.oppositePointHomDiagramIso F)).inv.w

/-- 概要：Kan 値図式の weighted nerve から、値を反転した coherent 図式の unstraightening への射。
方針：係数の同型の逆射を宇宙持ち上げし、反転した図式の標準比較に合成する。
規約：値の反転を定義域と混同せず、底は同じ nerve の持ち上げ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の復元比較の実際の射。 -/
noncomputable def oppositeKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (oppositePointHomWeightedIso F).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor)

/-- 概要：値を反転した coherent 図式への比較射は元の weighted nerve の射影を被覆する。
方針：標準比較の底上の可換性と、係数の同型の底上の可換性を合成する。
規約：射影と全空間をともに u+1 へ持ち上げる。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、復元の底上の比較。 -/
lemma oppositeKanUnstraighteningComparison_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    oppositeKanUnstraighteningComparison F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor)) =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) := by
  rw [oppositeKanUnstraighteningComparison, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison_projection, ← Functor.map_comp,
    oppositePointHomWeightedIso_inv_projection]

/-- 概要：元の係数の weighted nerve から値を反転した coherent 図式の unstraightening への射は前合成同値。
方針：係数の同型の持ち上げと標準比較の同値性を合成する。
規約：同値は実際の底上の比較射の性質として記録する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な図式の coherent な全空間への復元。 -/
lemma oppositeKanUnstraighteningComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (oppositeKanUnstraighteningComparison F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (oppositePointHomWeightedIso F).symm)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison_isPrecompositionEquivalence (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
