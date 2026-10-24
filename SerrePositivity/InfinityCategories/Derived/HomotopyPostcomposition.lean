module
public import SerrePositivity.InfinityCategories.Core.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

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
namespace SerrePositivity.InfinityCategories
/-- 全後合成作用を指定関手で評価すると、その関手による前合成。 -/
lemma functorPostcompositionMap_evaluate {K X Y : SSet.{u}} (f : K ⟶ X) :
    functorPostcompositionMap K X Y ≫ evaluateFunctorAt (functorVertex f) = (pre f).app Y := by
  change curry (MonoidalClosed.comp K X Y) ≫
    evaluateFunctorAt (SSet.unitHomEquiv _ (curry' f)) = _
  rw [curry_evaluateFunctorAt_unitHomEquiv]
  rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]
/-- 任意の実ホモトピーを、全パラメータ関手圏上の同じ後合成ホモトピーへ移す。 -/
noncomputable def homotopyPostcomposition {X Y : SSet.{u}} (K : SSet.{u})
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy ((ihom K).map f) ((ihom K).map g) := by
  let a := (functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (functorPostcompositionMap K X Y))
  let b : Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom K).obj X)).obj ((ihom K).obj Y)))
      (functorVertex ((ihom K).map f)) (functorVertex ((ihom K).map g)) := {
    edge := a.edge
    src_eq := a.src_eq.trans (functorPostcompositionMap_vertex f)
    tgt_eq := a.tgt_eq.trans (functorPostcompositionMap_vertex g) }
  exact simplicialHomotopyOfFunctorEdge b
end SerrePositivity.InfinityCategories
