module
public import SerrePositivity.InfinityCategories.Stable.StableVertexClosure
public import SerrePositivity.InfinityCategories.Stable.CofiberRotationConnecting

/-! # 実 cofiber 列に沿う安定閉包の拡大閉性

概要：実 cofiber 列の両端が安定閉包に属すると中間頂点も属する。
方針：実回転長方形で中間頂点を cofiber から suspension への fiber と表す。
規約：h の三角構造の引き戻しを使わない。使われ方：Verdier 分母の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}} [Quasicategory X] [IsStable X]

omit [Quasicategory X] [IsStable X] in
/-- 実 suspension は指定頂点の安定閉包を保つ。 -/
lemma StableVertexClosure.suspension (P : Set (X _⦋0⦌))
    {x : X _⦋0⦌} (s : SuspensionSquare x) (hx : StableVertexClosure P x) :
    StableVertexClosure P s.vertex := by
  apply StableVertexClosure.of_cofiber s.toZeroTriangle s.isPushout
  · exact s.source_eq.symm ▸ hx
  · exact StableVertexClosure.of_zero s.other_zero

/-- 実 cofiber 列の両端の所属から、中間頂点の所属を得る。 -/
lemma StableVertexClosure.extension (P : Set (X _⦋0⦌))
    (t : ZeroTriangle X) (ht : IsCofiberSequence t)
    (h₀ : StableVertexClosure P (squareVertex t.square 0 0))
    (h₂ : StableVertexClosure P (squareVertex t.square 1 1)) :
    StableVertexClosure P (squareVertex t.square 1 0) := by
  let r := chosenCofiberRotationRectangle t ht
  have hs := StableVertexClosure.suspension P r.suspensionSquare h₀
  have hm : StableVertexClosure P (squareVertex r.rotatedZeroTriangle.square 1 0) :=
    r.rotated_middle.symm ▸ h₂
  have he : StableVertexClosure P (squareVertex r.rotatedZeroTriangle.square 1 1) :=
    r.rotated_target.symm ▸ hs
  have hf := StableVertexClosure.of_fiber r.rotatedZeroTriangle
    (IsStable.pullback_of_pushout _ r.rotated_isCofiber) hm he
  exact r.rotated_source ▸ hf

end SerrePositivity.InfinityCategories
