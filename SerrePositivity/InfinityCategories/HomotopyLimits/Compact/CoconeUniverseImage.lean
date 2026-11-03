module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.Compact.RepresentationDiagramComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.Compact.UniverseCoconeRepresentations
public import SerrePositivity.InfinityCategories.F1.Compact.YonedaEvaluationClassification
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftFibration

/-!
概要：指定した宇宙変更による元の同じ余錐像と、図式部分への実比較を固定する。
方針：元の余錐の持ち上げへの後合成と、同じ表現の図式の厳密な等式を使う。
規約：余錐・頂点・全図式・全空間の比較を同時に保持。
使われ方：元の指定 fiber 写像と、元の宇宙変更後の指定 fiber 写像との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の指定余錐そのものを、指定した同じ空間の宇宙変更で送った余錐。 -/
def coconeUniverseImage (c : JoinCocone F) :
    JoinCocone ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) :=
  mapJoinCocone spaceUniverseDiagram (JoinCocone.ulift.{u + 1, u + 2} c)

/-- 余錐像の指定頂点は、元の指定頂点の同じ宇宙変更。 -/
lemma coconeUniverseImage_vertex (c : JoinCocone F) :
    (coconeUniverseImage c).vertex =
      spaceUniverseDiagram.app _ (ULift.up c.vertex) := rfl

/-- 余錐像の全写像は、元の余錐形状の実同型を通した元の同じ全写像。 -/
lemma coconeUniverseImage_val (c : JoinCocone F) :
    (coconeUniverseImage c).val = (uliftCoconeShapeIso.{u + 1, u + 2} B 0).inv ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map c.val ≫ spaceUniverseDiagram.{u} := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc]

variable [Quasicategory B]

/-- 同じ全余錐の表現を、元の宇宙変更図式そのものの全空間へ制限する。 -/
def coconeUniverseSourceComparison (c : JoinCocone F) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (leftUnstraightening F) ⟶
      leftUnstraightening
        ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) :=
  representationDiagramComparison (spaceUniverseCoconeSourceRepresentation c) _
    (spaceUniverseCoconeSourceRepresentation_diagram c)

/-- 元の図式への実比較は、同じ元の pointed 写像を保持する。 -/
lemma coconeUniverseSourceComparison_pointed (c : JoinCocone F) :
    coconeUniverseSourceComparison c ≫ pullback.fst pointedSpaceProjection
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) =
        (spaceUniverseCoconeSourceRepresentation c).pointedMap :=
  representationDiagramComparison_pointed _ _ _

/-- 元の図式への実比較は、同じ持ち上げた元の射影を保持する。 -/
lemma coconeUniverseSourceComparison_projection (c : JoinCocone F) :
    coconeUniverseSourceComparison c ≫ leftUnstraighteningProjection
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) =
        (SSet.uliftFunctor.{u + 2, u + 1}).map (leftUnstraighteningProjection F) :=
  representationDiagramComparison_projection _ _ _

/-- 元の図式への同じ実比較自身は、全空間の前合成同値。 -/
lemma coconeUniverseSourceComparison_isPrecompositionEquivalence (c : JoinCocone F) :
    IsPrecompositionEquivalence (coconeUniverseSourceComparison c) :=
  representationDiagramComparison_isPrecompositionEquivalence _ _ _

end SerrePositivity.InfinityCategories.F2.Compact
