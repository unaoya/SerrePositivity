module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTransportRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningOppositeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallFiberStraighteningCounit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction

/-!
概要：通常の nerve 上の strict transport と任意の相対表現の図式の比較。
方針：標準表現との比較を可縮な表現空間から取り、Kan 係数の反転比較と合成する。
規約：対象の fiber ごとの同値ではなく、底全体の関手同型を構成する。
使われ方：初頂点制限を経由した実際の straightening と表現の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 通常の nerve 上の反転係数の transport は、同じ射影の任意の表現の図式と同型。 -/
def nerveCoherentTransportRepresentationIso {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) R.diagram := by
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((SSet.uliftFunctor.{u + 1, u}).obj E |>.obj n) := by
    change Small.{u} (ULift.{u + 1} (E.obj n))
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberTransportRepresentationDiagramIso _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasSmallSimplexFibers_of_small_total _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nerveLeftTransportRepresentation p) R

/-- 通常の nerve 上の strict transport と任意の表現を同じ共同係数比較から比較する。 -/
def nerveStraighteningRepresentationIso {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) R.diagram :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap_oppositeVertexIso p ≪≫ nerveCoherentTransportRepresentationIso p R

/-- 宇宙の持ち上げは pullback を保つ。表現の制限に使う局所的な構造定理。 -/
lemma ulift_isPullback {E B D : SSet.{u}} (p : E ⟶ B) (g : D ⟶ B) :
    IsPullback ((SSet.uliftFunctor.{u + 1, u}).map (pullback.fst p g))
      ((SSet.uliftFunctor.{u + 1, u}).map (pullback.snd p g))
      ((SSet.uliftFunctor.{u + 1, u}).map p) ((SSet.uliftFunctor.{u + 1, u}).map g) := by
  have : PreservesLimitsOfShape WalkingCospan (SSet.uliftFunctor.{u + 1, u}) := by
    apply preservesLimitsOfShape_of_evaluation
    intro n
    change PreservesLimitsOfShape WalkingCospan
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n ⋙ CategoryTheory.uliftFunctor)
    infer_instance
  exact (IsPullback.of_hasPullback p g).map _

local instance {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 元の小さい pullback に沿い、持ち上げた射影の表現を厳密に制限する。 -/
def LeftTransportRepresentation.nativeRestrict {E B D : SSet.{u}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation
      ((SSet.uliftFunctor.{u + 1, u}).map (pullback.snd p g)) :=
  R.cartesianRestrict ((SSet.uliftFunctor.{u + 1, u}).map (pullback.fst p g))
    ((SSet.uliftFunctor.{u + 1, u}).map g) (ulift_isPullback p g)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentation (nativeRestrict)


/-- この制限の図式は、持ち上げた底の射との前合成そのもの。 -/
lemma LeftTransportRepresentation.nativeRestrict_diagram {E B D : SSet.{u}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) (g : D ⟶ B) :
    (R.nativeRestrict g).diagram = (SSet.uliftFunctor.map g) ≫ R.diagram := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentation (nativeRestrict_diagram)


/-- 同じ制限は全空間から pointed space への射も厳密に回収する。 -/
lemma LeftTransportRepresentation.nativeRestrict_pointedMap {E B D : SSet.{u}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) (g : D ⟶ B) :
    (R.nativeRestrict g).pointedMap =
      (SSet.uliftFunctor.map (pullback.fst p g)) ≫ R.pointedMap :=
  R.cartesianRestrict_pointedMap _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentation (nativeRestrict_pointedMap)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
