module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：指定実ホモトピーを、全パラメータ関手圏の後合成の実ホモトピーへ移す。
方針：閉構造の合成で関手辺を写し、同じ辺を uncurry する。
規約：quasicategory 性・有限性を仮定しない。使われ方：実 slice の普遍評価の族。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof
/-- 全後合成作用を指定関手で評価すると、その関手による前合成。 -/
lemma functorPostcompositionMap_evaluate {K X Y : SSet.{u}} (f : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap K X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) = (pre f).app Y := by
  change curry (MonoidalClosed.comp K X Y) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.unitHomEquiv _ (curry' f)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.curry_evaluateFunctorAt_unitHomEquiv]
  rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]
/-- 任意の実ホモトピーを、全パラメータ関手圏上の同じ後合成ホモトピーへ移す。 -/
noncomputable def homotopyPostcomposition {X Y : SSet.{u}} (K : SSet.{u})
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy ((ihom K).map f) ((ihom K).map g) := by
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap K X Y))
  let b : Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom K).obj X)).obj ((ihom K).obj Y)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((ihom K).map f)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((ihom K).map g)) := {
    edge := a.edge
    src_eq := a.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap_vertex f)
    tgt_eq := a.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap_vertex g) }
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge b
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof
