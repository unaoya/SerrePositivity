module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFiberCocone
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRelativeFiber

/-!
概要：大域図式の族の相対始点境界充填から各 fiber の余錐の相対普遍性を回収する。
方針：充填を底の fiber に制限し、相対比較の始域・標的の同型の逆で移す。
規約：p と U の充填性は不要。
使われ方：coherent に組み立てた相対 Kan 図式の局所相対条件の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：全空間の相対充填性から各 fiber の余錐の相対充填性が従う。
方針：fiber の相対比較を通常の相対余錐制限と同定し、二つの逆同型で条件を戻す。
規約：ここでの相対普遍性は操作的な始点境界充填条件。
使われ方：大域的な相対 Kan 図式が全ての局所相対余錐条件を満たすことの確認。 -/
lemma kanRelativeJoinFiberCocone_relative_of_initialBoundary {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E) (c : C _⦋0⦌) (H : relativeJoin p (𝟙 C) ⟶ D)
    (hx : InitialBoundaryLifting (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U)
      ((kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H).app
        (Opposite.op ⦋0⦌) c)) : KanRelativeCoconeLifting U (kanRelativeJoinFiberCocone p c H) := by
  let e := kanRelativeJoinCoconeFiberIso p c D
  let t := kanRelativeJoinRelativeTargetFiberIso p c U
  let z := kanRelativeJoinFiberCocone p c H
  let x := e.hom.app (Opposite.op ⦋0⦌) (functorVertex z.val)
  have hxt : InitialBoundaryLifting
      (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U) x.val := by
    change InitialBoundaryLifting _
      (((kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
        (functorVertex (kanRelativeJoinFiberCocone p c H).val)).val)
    rw [kanRelativeJoinFiberCocone_family_vertex]
    exact hx
  have hxf := SerrePositivity.InfinityCategories.F1B.initialBoundaryLifting_fiber_of_total
    (SerrePositivity.InfinityCategories.fiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D)
    (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeProjection (kanRelativeJoinInlOver p) U)
    (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U)
    (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_projection (kanRelativeJoinInlOver p) U) c x hxt
  have he : e.inv ≫ kanRelativeCoconeRestriction (vertexFiber p c) U =
      SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestrictionFiber (kanRelativeJoinInlOver p) U c ≫ t.inv := by
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
      kanRelativeJoinRelativeFiber_restriction, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hm := hxf.map_iso e.symm t.symm he
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app e.hom_inv_id (Opposite.op ⦋0⦌)) (functorVertex z.val)
  change e.inv.app (Opposite.op ⦋0⦌) x = functorVertex z.val at hv
  change InitialBoundaryLifting (kanRelativeCoconeRestriction (vertexFiber p c) U)
    (e.inv.app (Opposite.op ⦋0⦌) x) at hm
  rw [hv] at hm
  exact hm

end SerrePositivity.InfinityCategories.F1B
