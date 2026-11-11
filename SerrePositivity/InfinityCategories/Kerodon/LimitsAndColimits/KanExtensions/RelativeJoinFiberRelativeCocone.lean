module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFiberCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRelativeFiber

/-!
概要：大域図式の族の相対始点境界充填から各 fiber の余錐の相対普遍性を回収する。
方針：充填を底の fiber に制限し、相対比較の始域・標的の同型の逆で移す。
規約：p と U の充填性は不要。
使われ方：coherent に組み立てた相対 Kan 図式の局所相対条件の回収。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：全空間の相対充填性から各 fiber の余錐の相対充填性が従う。
方針：fiber の相対比較を通常の相対余錐制限と同定し、二つの逆同型で条件を戻す。
規約：ここでの相対普遍性は操作的な始点境界充填条件。
使われ方：大域的な相対 Kan 図式が全ての局所相対余錐条件を満たすことの確認。 -/
lemma kanRelativeJoinFiberCocone_relative_of_initialBoundary {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E) (c : C _⦋0⦌) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseRelativeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) U)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) H).app
        (Opposite.op ⦋0⦌) c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c H) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p c D
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeTargetFiberIso p c U
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c H
  let x := e.hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)
  have hxt : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseRelativeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) U) x.val := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting _
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c H).val)).val)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone_family_vertex]
    exact hx
  have hxf := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_fiber_of_total
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseRelativeProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) U)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseRelativeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) U)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseRelativeRestriction_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) U) c x hxt
  have he : e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) U =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseRelativeRestrictionFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) U c ≫ t.inv := by
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeFiber_restriction, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hm := hxf.map_iso e.symm t.symm he
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app e.hom_inv_id (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)
  change e.inv.app (Opposite.op ⦋0⦌) x = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val at hv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) U)
    (e.inv.app (Opposite.op ⦋0⦌) x) at hm
  rw [hv] at hm
  exact hm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
