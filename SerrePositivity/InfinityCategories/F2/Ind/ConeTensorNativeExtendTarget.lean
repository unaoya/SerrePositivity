module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorExtendTarget
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorTargetUniverse

/-!
概要：同じ補間領域の余錐を元の大きい積へ戻しても、指定終点面を厳密に回収する。
方針：終点面の宇宙比較で相殺し、元の全拡張の点面を用いる。
規約：余錐・点・包含を変更しない。
使われ方：scalar comma の指定変換下の相対余錐を全終点拡張へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の大きい全拡張の終点面は指定部分の同じ全余錐。
方針：宇宙比較を相殺。規約：全射の等号。使われ方：指定変換の全延長。 -/
lemma coneTensorNativeExtend_target {A L : SSet.{u}} {X : SSet.{u + 1}}
    {H : (SSet.uliftFunctor.{u + 1, u}).obj (coneTensorCorner A L) ⟶ X}
    (c : JoinCocone H) :
    tensorRightPoint (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0])
      (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
        (inv (coneTensorUniverseShape A L) ≫ coneTensorExtend c) =
    joinMap ((SSet.uliftFunctor.{u + 1, u}).map (coneTensorTargetInclusion A L))
      (𝟙 (Δ[0] : SSet.{u + 1})) ≫ c.val := by
  apply (cancel_epi (uliftCoconeShapeIso.{u, u + 1} A 0).hom).mp
  rw [← Category.assoc, ← coneTensorUniverseShape_target, Category.assoc,
    IsIso.hom_inv_id_assoc, coneTensorExtend_target]
end SerrePositivity.InfinityCategories.F2.Ind
