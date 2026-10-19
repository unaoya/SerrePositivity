module

public import SerrePositivity.InfinityCategories.F1B.KanGlobalDiagramFamily
public import SerrePositivity.InfinityCategories.F1B.KanInitialBoundaryFiberRestriction
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinCoconeFiber

/-!
概要：相対 join の図式の各 fiber の余錐を取り出し、相対始点充填から余極限性を回収する。
方針：fiber の join 表示と関手空間の同型を使い、充填を fiber に制限して余錐制限へ戻す。
規約：余極限性には標的の quasicategory 性だけを使う。
使われ方：coherent に組み立てた図式から点ごとの Kan 条件を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対 join 上の図式を底の一つの fiber へ制限した余錐。
方針：fiber と通常の join の同型を図式に前合成する。
規約：底の局所 slice 全体の余錐とは区別する。
使われ方：組み立てた普遍余錐の fiber ごとの回収。 -/
def kanRelativeJoinFiberCocone {K C D : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌)
    (H : relativeJoin p (𝟙 C) ⟶ D) :
    JoinCocone (vertexFiberι p c ≫ relativeJoinInl p (𝟙 C) ≫ H) :=
  ⟨(kanRelativeJoinBaseFiberIso p c).hom ≫
    vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c ≫ H, by
      rw [← Category.assoc, kanRelativeJoinBaseFiberIso_inl, ← Category.assoc, vertexFiberMap_ι,
        Category.assoc]⟩

/-- 概要：取り出した fiber の余錐の関手頂点は大域図式の族の同じ頂点を表す。
方針：join の fiber の同型の往復と、大域図式の族の fiber 比較を使う。
規約：関手空間の fiber の包含後の厳密な式。
使われ方：全空間の境界充填を実際の fiber の余錐に適用する。 -/
lemma kanRelativeJoinFiberCocone_family_vertex {K C D : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (H : relativeJoin p (𝟙 C) ⟶ D) :
    ((kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
      (functorVertex (kanRelativeJoinFiberCocone p c H).val)).val =
        (kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H).app
          (Opposite.op ⦋0⦌) c := by
  change ((kanFiberwiseHomFiberIso (relativeJoinBaseProjection p (𝟙 C)) c D).hom.app
    (Opposite.op ⦋0⦌) (functorVertex ((kanRelativeJoinBaseFiberIso p c).inv ≫
      (kanRelativeJoinBaseFiberIso p c).hom ≫
        vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c ≫ H))).val = _
  rw [Iso.inv_hom_id_assoc]
  exact kanGlobalDiagramFamily_fiber_vertex (relativeJoinBaseProjection p (𝟙 C)) H c

/-- 概要：大域図式の族の相対始点境界充填から各 fiber の余錐の余極限性が従う。
方針：充填を底の fiber に制限し、二つの関手空間の同型の逆で余錐制限へ戻す。
規約：p の cocartesian 性は必要ない。
使われ方：局所余極限から作った図式の普遍性を取り戻す。 -/
lemma kanRelativeJoinFiberCocone_isColimit_of_initialBoundary {K C D : SSet.{u}}
    [Quasicategory D] (p : K ⟶ C) (c : C _⦋0⦌) (H : relativeJoin p (𝟙 C) ⟶ D)
    (hx : InitialBoundaryLifting (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
      ((kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H).app
        (Opposite.op ⦋0⦌) c)) : IsColimitCone (kanRelativeJoinFiberCocone p c H) := by
  let e := kanRelativeJoinCoconeFiberIso p c D
  let d := kanFiberwiseHomFiberIso p c D
  let z := kanRelativeJoinFiberCocone p c H
  let x := e.hom.app (Opposite.op ⦋0⦌) (functorVertex z.val)
  have hxt : InitialBoundaryLifting
      (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)) x.val := by
    change InitialBoundaryLifting _
      (((kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
        (functorVertex (kanRelativeJoinFiberCocone p c H).val)).val)
    rw [kanRelativeJoinFiberCocone_family_vertex]
    exact hx
  have hxf := kanInitialBoundaryLifting_fiber_of_total
    (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D)
    (kanFiberwiseHomProjection p D) (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
    (kanFiberwiseHomPre_projection (D := D) (kanRelativeJoinInlOver p)) c x hxt
  have he : e.inv ≫ coconeRestriction (vertexFiber p c) D =
      kanFiberwiseHomPreFiber (D := D) (kanRelativeJoinInlOver p) c ≫ d.inv := by
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
      kanRelativeJoinCoconeFiberIso_restriction, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hm := hxf.map_iso e.symm d.symm he
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app e.hom_inv_id (Opposite.op ⦋0⦌)) (functorVertex z.val)
  change e.inv.app (Opposite.op ⦋0⦌) x = functorVertex z.val at hv
  change InitialBoundaryLifting (coconeRestriction (vertexFiber p c) D)
    (e.inv.app (Opposite.op ⦋0⦌) x) at hm
  rw [hv] at hm
  exact isColimitCone_of_initialBoundaryLifting_coconeRestriction z hm

end SerrePositivity.InfinityCategories.F1B
