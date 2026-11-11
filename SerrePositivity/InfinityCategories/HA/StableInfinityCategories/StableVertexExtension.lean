module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationConnecting

/-! # 実 cofiber 列に沿う安定閉包の拡大閉性

概要：実 cofiber 列の両端が安定閉包に属すると中間頂点も属する。
方針：実回転長方形で中間頂点を cofiber から suspension への fiber と表す。
規約：h の三角構造の引き戻しを使わない。使われ方：Verdier 分母の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

omit [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] in
/-- 実 suspension は指定頂点の安定閉包を保つ。 -/
lemma StableVertexClosure.suspension (P : Set (X _⦋0⦌))
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P s.vertex := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_cofiber s.toZeroTriangle s.isPushout
  · exact s.source_eq.symm ▸ hx
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_zero s.other_zero

/-- 実 cofiber 列の両端の所属から、中間頂点の所属を得る。 -/
lemma StableVertexClosure.extension (P : Set (X _⦋0⦌))
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0))
    (h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0) := by
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberRotationRectangle t ht
  have hs := StableVertexClosure.suspension P r.suspensionSquare h₀
  have hm : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex r.rotatedZeroTriangle.square 1 0) :=
    r.rotated_middle.symm ▸ h₂
  have he : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex r.rotatedZeroTriangle.square 1 1) :=
    r.rotated_target.symm ▸ hs
  have hf := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_fiber r.rotatedZeroTriangle
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout _ r.rotated_isCofiber) hm he
  exact r.rotated_source ▸ hf

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
