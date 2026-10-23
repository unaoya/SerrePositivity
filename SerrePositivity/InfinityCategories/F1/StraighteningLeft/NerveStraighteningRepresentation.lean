module

public import SerrePositivity.InfinityCategories.F1.Transport.NerveTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningOppositeComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallFiberStraighteningCounit
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationCartesianRestriction

/-!
概要：通常の nerve 上の strict transport と任意の相対表現の図式の比較。
方針：標準表現との比較を可縮な表現空間から取り、Kan 係数の反転比較と合成する。
規約：対象の fiber ごとの同値ではなく、底全体の関手同型を構成する。
使われ方：初頂点制限を経由した実際の straightening と表現の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 通常の nerve 上の反転係数の transport は、同じ射影の任意の表現の図式と同型。 -/
def nerveCoherentTransportRepresentationIso {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
    FunctorIso (leftCoherentTransport p) R.diagram := by
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((SSet.uliftFunctor.{u + 1, u}).obj E |>.obj n) := by
    change Small.{u} (ULift.{u + 1} (E.obj n))
    infer_instance
  exact smallFiberTransportRepresentationDiagramIso _
    (hasSmallSimplexFibers_of_small_total _) (nerveLeftTransportRepresentation p) R

/-- 通常の nerve 上の strict transport と任意の表現を同じ共同係数比較から比較する。 -/
def nerveStraighteningRepresentationIso {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
    FunctorIso (leftStraighteningCandidate p) R.diagram :=
  leftStraighteningCoherentMap_oppositeVertexIso p ≪≫ nerveCoherentTransportRepresentationIso p R

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

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 元の小さい pullback に沿い、持ち上げた射影の表現を厳密に制限する。 -/
def LeftTransportRepresentation.nativeRestrict {E B D : SSet.{u}}
    {p : E ⟶ B} [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) (g : D ⟶ B) :
    LeftTransportRepresentation
      ((SSet.uliftFunctor.{u + 1, u}).map (pullback.snd p g)) :=
  R.cartesianRestrict ((SSet.uliftFunctor.{u + 1, u}).map (pullback.fst p g))
    ((SSet.uliftFunctor.{u + 1, u}).map g) (ulift_isPullback p g)

/-- この制限の図式は、持ち上げた底の射との前合成そのもの。 -/
lemma LeftTransportRepresentation.nativeRestrict_diagram {E B D : SSet.{u}}
    {p : E ⟶ B} [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) (g : D ⟶ B) :
    (R.nativeRestrict g).diagram = (SSet.uliftFunctor.map g) ≫ R.diagram := rfl

/-- 同じ制限は全空間から pointed space への射も厳密に回収する。 -/
lemma LeftTransportRepresentation.nativeRestrict_pointedMap {E B D : SSet.{u}}
    {p : E ⟶ B} [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) (g : D ⟶ B) :
    (R.nativeRestrict g).pointedMap =
      (SSet.uliftFunctor.map (pullback.fst p g)) ≫ R.pointedMap :=
  R.cartesianRestrict_pointedMap _ _ _

end SerrePositivity.InfinityCategories
