module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：指定した実境界比較辺を選び直さず、全図式の境界を厳密化する。
方針：制限射の実可逆辺持ち上げを使い、同じ全円柱の制限として境界比較を回収する。
規約：FunctorIso から代表辺を再選択せず、入力の一次単体を厳密に保持する。
使われ方：c5 の元の図式側で定値な実比較を保つ次元延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の境界比較の実一次単体を保持する全図式の厳密化。 -/
structure SpecifiedBoundaryEdgeNormalization {K L X : SSet.{u}}
    (j : K ⟶ L) (F : L ⟶ X) (G : K ⟶ X)
    (a : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) where
  diagram : L ⟶ X
  boundary : j ≫ diagram = G
  edge : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex diagram)
  isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge edge.toTruncated
  restriction : ((pre j).app X).app (Opposite.op ⦋1⦌) edge.edge = a.edge

namespace SpecifiedBoundaryEdgeNormalization
variable {K L X : SSet.{u}} {j : K ⟶ L} {F : L ⟶ X} {G : K ⟶ X}
  {a : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)}
  (d : SpecifiedBoundaryEdgeNormalization j F G a)

def homotopy : SSet.Homotopy F d.diagram := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge d.edge.toTruncated

/-- 厳密化の全円柱は、元の実境界比較円柱そのものに制限する。 -/
lemma homotopy_restriction :
    (j ▷ (Δ[1] : SSet.{u})) ≫ d.homotopy.h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge a.toTruncated).h := by
  change (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm d.edge.edge) = _
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm
    (((pre j).app X).app (Opposite.op ⦋1⦌) d.edge.edge)) = _
  rw [d.restriction]
  rfl

end SpecifiedBoundaryEdgeNormalization

private lemma boundaryEdge_target {E Y : SSet.{u}} (p : E ⟶ Y) (v : E _⦋1⦌) :
    p.app (Opposite.op ⦋0⦌) (E.δ 0 v) = Y.δ 0 (p.app (Opposite.op ⦋1⦌) v) :=
  ConcreteCategory.congr_hom (C := Type u)
    (p.naturality (SimplexCategory.δ (0 : Fin 2)).op) v

/-- 元の可逆境界辺の実一次単体を変えず、全図式をその標的境界へ厳密化する。 -/
lemma exists_specifiedBoundaryEdgeNormalization {K L X : SSet.{u}} [Quasicategory X]
    (j : K ⟶ L) [Mono j] (F : L ⟶ X) (G : K ⟶ X)
    (a : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a) :
    Nonempty (SpecifiedBoundaryEdgeNormalization j F G a) := by
  obtain ⟨F', l, hl, hli⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pre_liftInvertibleEdge_source j F G a ha
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F') = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G := by
    calc
      _ = ((pre j).app X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F') := rfl
      _ = ((pre j).app X).app (Opposite.op ⦋0⦌)
          (((ihom L).obj X).δ 0 l.edge) := congrArg _ l.tgt_eq.symm
      _ = ((ihom K).obj X).δ 0 (((pre j).app X).app (Opposite.op ⦋1⦌) l.edge) :=
        @boundaryEdge_target ((ihom L).obj X) ((ihom K).obj X) ((pre j).app X) l.edge
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G := by rw [hl]; exact a.tgt_eq
  exact ⟨⟨F', _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective hp, l, hli, hl⟩⟩

end SerrePositivity.KST.LocalizingInvariants
