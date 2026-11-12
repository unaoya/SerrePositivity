module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndConeEndpointCommaIso

/-!
概要：元の余錐の指定頂点を持ち上げた点は、同じ宇宙比較で元の右頂点へ厳密に移る。
方針：元の右包含の Yoneda 表示と、証明済みの宇宙比較の右包含則を合成する。
規約：元の指定点と全包含を保持する。
使われ方：再構成した終点面を、元の極大点評価と同定する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の余錐点の全点写像は、元の右包含そのもの。
方針：元の零単体の Yoneda 表示。規約：同じ点と全射。使われ方：終点面の同定。 -/
lemma coneApex_point (L : SSet.{u}) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex L) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr L (Δ[0] : SSet.{u}) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  have hp : (stdSimplex.obj₀Equiv.symm 0 : (Δ[0] : SSet.{u}) _⦋0⦌) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply SSet.stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  exact congrArg (fun x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr L (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) x) hp
/-- 概要：元の指定余錐点の持ち上げは、宇宙比較後も同じ元の右包含。
方針：元の右包含の宇宙比較と点の持ち上げ。規約：全射の等号。使われ方：評価面の同定。 -/
lemma indConeShape_point (L : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramShapePoint (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex L) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, u + 1} L 0).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeShape_inv_inr (L := L)
  rw [← coneApex_point L, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramShapePoint, ← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
