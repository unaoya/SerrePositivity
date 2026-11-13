module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluationFrames
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits

/-!
概要：実frameの全自然変換を、評価した全二変数Homのendとして構成する。
方針：元の各自然変換の成分でwedgeを作り、その全単体での普遍性を証明する。
規約：この特定のendのKan性は、図式圏でのframeのKan性から得る。
使われ方：Hovey §5.4、HTT 4.2.4.4の全変換空間のendによる表示。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

/-- 同じ図式のframe Homを、同じ各頂点のHomへ送る成分写像。 -/
def strictDiagramPointFrameProjection (X Y : StrictComplexDiagram A d)
    (j : strictDiagramIndex d) :
    strictDiagramFrameMapping A d X Y ⟶
      ((strictDiagramPointFrameMapping A d X Y).obj (Opposite.op j)).obj j where
  app _ := ↾fun f => f.app j
  naturality := by intros; rfl

/-- 元の全自然変換の成分は、全添字射の自然性を保つwedgeをなす。 -/
def strictDiagramPointFrameEndWedge (X Y : StrictComplexDiagram A d) :
    Wedge (strictDiagramPointFrameMapping A d X Y) :=
  Wedge.mk (strictDiagramFrameMapping A d X Y)
    (strictDiagramPointFrameProjection A d X Y) (by
      intro i j a
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro f
      exact (f.naturality a).symm)

/-- 任意の全単体的wedgeの成分を、同じ各次数の自然変換として束ねる。 -/
def strictDiagramPointFrameEndLift (X Y : StrictComplexDiagram A d)
    (s : Wedge (strictDiagramPointFrameMapping A d X Y)) :
    s.pt ⟶ strictDiagramFrameMapping A d X Y where
  app n := ↾fun z =>
    { app := fun j => (s.ι j).app n z
      naturality := by
        intro i j a
        exact (congrArg (fun f => f.app n z) (s.condition a)).symm }
  naturality {m n} θ := by
    apply ConcreteCategory.hom_ext
    intro z
    apply NatTrans.ext
    funext j
    exact congrArg (fun f => f z) ((s.ι j).naturality θ)

/-- 全成分での自然変換の外延性により、同じwedgeは実際に極限である。 -/
def strictDiagramPointFrameEndIsLimit (X Y : StrictComplexDiagram A d) :
    IsLimit (strictDiagramPointFrameEndWedge A d X Y) :=
  Multifork.IsLimit.mk (strictDiagramPointFrameEndWedge A d X Y)
    (strictDiagramPointFrameEndLift A d X Y)
    (by
      intro s j
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      rfl)
    (by
      intro s m hm
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      apply NatTrans.ext
      funext j
      exact congrArg (fun f => f.app n z) (hm j))

/-- 元の全自然変換の単体集合と、評価した同じ二変数Homのendとの実同型。 -/
def strictDiagramPointFrameEndIso (X Y : StrictComplexDiagram A d) :
    strictDiagramFrameMapping A d X Y ≅ end_ (strictDiagramPointFrameMapping A d X Y) :=
  (strictDiagramPointFrameEndIsLimit A d X Y).conePointUniqueUpToIso (limit.isLimit _)

/-- このendは元のReedy frame Homと同型なのでKanである。一般のendへの主張ではない。 -/
lemma strictDiagramPointFrameEnd_kanComplex (X Y : StrictComplexDiagram A d) :
    KanComplex (end_ (strictDiagramPointFrameMapping A d X Y)) := by
  haveI := strictDiagramFrameMapping_kanComplex A d X Y
  exact kanComplex_of_iso (strictDiagramPointFrameEndIso A d X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
