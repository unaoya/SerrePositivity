module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorBaseChangeComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramJointComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionDiagram

/-!
概要：底変換の相対切断同型を、全添字と全対象の coherent な比較へ束ねる。
方針：各添字の底変換の豊穣比較と前合成の自然性を図式の比較として共同実現する。
規約：対象ごとの同型だけでなく全高次の実際の族を構成する。
使われ方：under の切断と初頂点写像で引き戻した strict transport の同定。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：底変換した切断と合成した定義域の切断を比べる豊穣図式の比較。
方針：各添字で元の底変換同型を使い、前合成との可換式を自然性にする。
規約：全対象と全添字で同じ同型を使う。
使われ方：共同実現の大域的な比較の入力。 -/
def relativeSectionBaseChangeComparison {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (A ⋙ Over.map k)) where
  component j := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorBaseChangeComparison k (A.obj (Opposite.op j))
  naturality f p := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorBaseChangeForward_overPre p.val.hom k (A.map f.op)

/-- 概要：切断の底変換の比較の各成分は元の同型による同値。
方針：相対関手空間の底変換同型の順方向を回収する。
規約：図式の比較の実際の成分を判定する。
使われ方：共同の比較の辺の可逆性。 -/
lemma relativeSectionBaseChangeComparison_isQCatEquivalence {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D)
    (j : J) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd p.val.hom k) (A.obj (Opposite.op j)).hom)
      (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.val.hom ((A.obj (Opposite.op j)).hom ≫ k))
      (((relativeSectionBaseChangeComparison k A).component j).val p) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p.val.hom k (A.obj (Opposite.op j)).hom)).isQCatEquivalence

/-- 概要：底変換と切断図式の共同実現は全パラメーター上で関手同型。
方針：底変換の豊穣図式の比較を実際の共同族に実現し、前合成の公式で始点を揃える。
規約：底にも添字にも追加の充填性の仮定を課さない。
使われ方：strict transport の分類との大域的な接続。 -/
def relativeSectionBaseChangeRealizationIso {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationInfinityBaseChange k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).realization)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (A ⋙ Over.map k)).realization := by
  have e := (relativeSectionBaseChangeComparison k A).realizationIso
    (relativeSectionBaseChangeComparison_isQCatEquivalence k A)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization_precompose] at e
  exact e

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
