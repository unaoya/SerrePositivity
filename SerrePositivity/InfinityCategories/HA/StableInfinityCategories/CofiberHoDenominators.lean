module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableHoTriangulated
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingBaseChange

/-! # 実 cofiber 分母と h C の Verdier 分母

概要：実安定閉包の cofiber 辺は h C の対応する三角的対象条件の trW と一致する。
方針：選んだ実 cofiber 三角形の第一射を指定辺の類と Arrow 上で厳密に照合する。
規約：対象・辺の宇宙を変更しない。使われ方：通常の分数計算を実辺へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory Pretriangulated SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 指定 cofiber 三角形の第一射は指定実辺の類と同じ Arrow。 -/
lemma CofiberSquare.triangle_first_arrow
    {x y : X _⦋0⦌} {f : Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle s.toZeroTriangle s.isPushout).mor₁ =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk f) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge, s.bottom_edge]
  exact SSet.yonedaEquiv.apply_symm_apply f.edge

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (triangle_first_arrow)


/-- 実辺の分母条件と、その類が三角的分母であることは同値。 -/
theorem cofiberStableEdges_iff_trW (P : Set (X _⦋0⦌))
    {x y : X _⦋0⦌} (f : Truncated.Edge (X := (truncation 2).obj X) x y) :
    f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW (SSet.Truncated.HomotopyCategory.homMk f) := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare f
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_edge_mem_iff P s]
  have h := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW_iff_of_distinguished
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle s.toZeroTriangle s.isPushout)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles _ _)
  have he := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW.arrow_mk_iso_iff (eqToIso s.triangle_first_arrow)
  exact h.symm.trans he

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
