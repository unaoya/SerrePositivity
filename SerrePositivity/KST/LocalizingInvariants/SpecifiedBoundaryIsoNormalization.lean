module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismEdgeLifting
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

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
    (j : K ⟶ L) (F : L ⟶ X) (G : K ⟶ X) (e : FunctorIso (j ≫ F) G) where
  diagram : L ⟶ X
  boundary : j ≫ diagram = G
  edge : SSet.Edge (X := (ihom L).obj X) (functorVertex F) (functorVertex diagram)
  isInvertible : IsInvertibleEdge (X := (ihom L).obj X) edge.toTruncated
  restriction : (((pre j).app X).app (Opposite.op ⦋1⦌) edge.edge) = (FunctorIso.edge e).edge

namespace SpecifiedBoundaryIsoNormalization
variable {K L X : SSet.{u}} [Quasicategory X]
  {j : K ⟶ L} {F : L ⟶ X} {G : K ⟶ X} {e : FunctorIso (j ≫ F) G}
  (d : SpecifiedBoundaryIsoNormalization j F G e)

/-- 同じ持ち上げ辺から取り出す全図式の同型。 -/
def iso : FunctorIso F d.diagram :=
  have : IsIso (Truncated.HomotopyCategory.homMk d.edge.toTruncated) := d.isInvertible
  asIso (Truncated.HomotopyCategory.homMk d.edge.toTruncated)

end SpecifiedBoundaryIsoNormalization

private lemma boundaryMap_edge_target {E Y : SSet.{u}} (p : E ⟶ Y) (v : E _⦋1⦌) :
    p.app (Opposite.op ⦋0⦌) (E.δ 0 v) = Y.δ 0 (p.app (Opposite.op ⦋1⦌) v) :=
  ConcreteCategory.congr_hom (C := Type u)
    (p.naturality (SimplexCategory.δ (0 : Fin 2)).op) v

/-- 指定された境界同型の辺を変えずに、全図式の境界を厳密化する。 -/
lemma exists_specifiedBoundaryIsoNormalization {K L X : SSet.{u}} [Quasicategory X]
    (j : K ⟶ L) [Mono j] (F : L ⟶ X) (G : K ⟶ X) (e : FunctorIso (j ≫ F) G) :
    Nonempty (SpecifiedBoundaryIsoNormalization j F G e) := by
  let a := SSet.Edge.ofTruncated (X := (ihom K).obj X) (FunctorIso.edge e)
  obtain ⟨F', l, hl, hli⟩ := pre_liftInvertibleEdge_source j F G a
    (FunctorIso.edge_isInvertible e)
  have hp : functorVertex (j ≫ F') = functorVertex G := by
    calc
      _ = ((pre j).app X).app (Opposite.op ⦋0⦌) (functorVertex F') := rfl
      _ = ((pre j).app X).app (Opposite.op ⦋0⦌)
          (((ihom L).obj X).δ 0 l.edge) := congrArg _ l.tgt_eq.symm
      _ = ((ihom K).obj X).δ 0 (((pre j).app X).app (Opposite.op ⦋1⦌) l.edge) :=
        @boundaryMap_edge_target ((ihom L).obj X) ((ihom K).obj X)
          ((pre j).app X) l.edge
      _ = functorVertex G := by rw [hl]; exact a.tgt_eq
  exact ⟨⟨F', functorVertex_injective hp, l, hli, hl⟩⟩

end SerrePositivity.KST.LocalizingInvariants
