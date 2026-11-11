module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalDiagramFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryFiberRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinCoconeFiber

/-!
概要：相対 join の図式の各 fiber の余錐を取り出し、相対始点充填から余極限性を回収する。
方針：fiber の join 表示と関手空間の同型を使い、充填を fiber に制限して余錐制限へ戻す。
規約：余極限性には標的の quasicategory 性だけを使う。
使われ方：coherent に組み立てた図式から点ごとの Kan 条件を得る。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対 join 上の図式を底の一つの fiber へ制限した余錐。
方針：fiber と通常の join の同型を図式に前合成する。
規約：底の局所 slice 全体の余錐とは区別する。
使われ方：組み立てた普遍余錐の fiber ごとの回収。 -/
def kanRelativeJoinFiberCocone {K C D : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C) ≫ H) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinBaseFiberIso p c).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) c ≫ H, by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinBaseFiberIso_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
        Category.assoc]⟩

/-- 概要：取り出した fiber の余錐の関手頂点は大域図式の族の同じ頂点を表す。
方針：join の fiber の同型の往復と、大域図式の族の fiber 比較を使う。
規約：関手空間の fiber の包含後の厳密な式。
使われ方：全空間の境界充填を実際の fiber の余錐に適用する。 -/
lemma kanRelativeJoinFiberCocone_family_vertex {K C D : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (kanRelativeJoinFiberCocone p c H).val)).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) H).app
          (Opposite.op ⦋0⦌) c := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) c D).hom.app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinBaseFiberIso p c).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinBaseFiberIso p c).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) c ≫ H))).val = _
  rw [Iso.inv_hom_id_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily_fiber_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) H c

/-- 概要：大域図式の族の相対始点境界充填から各 fiber の余錐の余極限性が従う。
方針：充填を底の fiber に制限し、二つの関手空間の同型の逆で余錐制限へ戻す。
規約：p の cocartesian 性は必要ない。
使われ方：局所余極限から作った図式の普遍性を取り戻す。 -/
lemma kanRelativeJoinFiberCocone_isColimit_of_initialBoundary {K C D : SSet.{u}}
    [Quasicategory D] (p : K ⟶ C) (c : C _⦋0⦌) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) H).app
        (Opposite.op ⦋0⦌) c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (kanRelativeJoinFiberCocone p c H) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p c D
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso p c D
  let z := kanRelativeJoinFiberCocone p c H
  let x := e.hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)
  have hxt : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p)) x.val := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting _
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (kanRelativeJoinFiberCocone p c H).val)).val)
    rw [kanRelativeJoinFiberCocone_family_vertex]
    exact hx
  have hxf := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_fiber_of_total
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPre_projection (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p)) c x hxt
  have he : e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPreFiber (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) c ≫ d.inv := by
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso_restriction, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hm := hxf.map_iso e.symm d.symm he
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app e.hom_inv_id (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)
  change e.inv.app (Opposite.op ⦋0⦌) x = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val at hv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) D)
    (e.inv.app (Opposite.op ⦋0⦌) x) at hm
  rw [hv] at hm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_initialBoundaryLifting_coconeRestriction z hm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
