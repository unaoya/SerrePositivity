module

public import SerrePositivity.KST.LocalizingInvariants.SpecifiedBoundaryEdgeNormalization

/-!
概要：指定された境界同型の同じ辺を保持して、全図式の境界を厳密化する。
方針：制限射の同値辺持ち上げを実適用し、持ち上げ辺と元の境界辺の一致を保持する。
規約：全図式の同型だけでなく、元の比較一次単体を選び直さず保存する。
使われ方：c5 の有限図式と尾部の貼合せで、指定商境界を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 指定境界辺を保つ全図式の厳密化。 -/
structure SpecifiedBoundaryIsoNormalization {K L X : SSet.{u}} [Quasicategory X]
    (j : K ⟶ L) (F : L ⟶ X) (G : K ⟶ X) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (j ≫ F) G) where
  diagram : L ⟶ X
  boundary : j ≫ diagram = G
  edge : SSet.Edge (X := (ihom L).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex diagram)
  isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom L).obj X) edge.toTruncated
  restriction : (((pre j).app X).app (Opposite.op ⦋1⦌) edge.edge) = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e).edge

namespace SpecifiedBoundaryIsoNormalization
variable {K L X : SSet.{u}} [Quasicategory X]
  {j : K ⟶ L} {F : L ⟶ X} {G : K ⟶ X} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (j ≫ F) G}
  (d : SpecifiedBoundaryIsoNormalization j F G e)

/-- 同じ持ち上げ辺から取り出す全図式の同型。 -/
def iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F d.diagram :=
  have : IsIso (Truncated.HomotopyCategory.homMk d.edge.toTruncated) := d.isInvertible
  asIso (Truncated.HomotopyCategory.homMk d.edge.toTruncated)

end SpecifiedBoundaryIsoNormalization

/-- 指定された境界同型の辺を変えずに、全図式の境界を厳密化する。 -/
lemma exists_specifiedBoundaryIsoNormalization {K L X : SSet.{u}} [Quasicategory X]
    (j : K ⟶ L) [Mono j] (F : L ⟶ X) (G : K ⟶ X) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (j ≫ F) G) :
    Nonempty (SpecifiedBoundaryIsoNormalization j F G e) := by
  let a := SSet.Edge.ofTruncated (X := (ihom K).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e)
  obtain ⟨d⟩ := exists_specifiedBoundaryEdgeNormalization j F G a
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible e)
  exact ⟨⟨d.diagram, d.boundary, d.edge, d.isInvertible, d.restriction⟩⟩

end SerrePositivity.KST.LocalizingInvariants
