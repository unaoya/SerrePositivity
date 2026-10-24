module
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareSpanPullback
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberSquareIso

/-!
概要：固定 span の余錐比較から suspension の普遍四角形と厳密切断を構成する。
方針：実 fiber の同型で始対象性を余極限性へ戻し、全境界持ち上げを使う。
規約：安定性・有限余極限は仮定しない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
def squareCoconeFunctorIso (X : SSet.{u}) :
    (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X ≅
      (ihom (join (horn 2 0 : SSet.{u}) (Δ[0] : SSet.{u}))).obj X where
  hom := (pre spanCoconeSquareIso.hom).app X
  inv := (pre spanCoconeSquareIso.inv).app X
  hom_inv_id := by
    simp only [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id, NatTrans.id_app]
  inv_hom_id := by
    simp only [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id, NatTrans.id_app]

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma squareCoconeFunctorIso_restriction (X : SSet.{u}) :
    (squareCoconeFunctorIso X).hom ≫ coconeRestriction (horn 2 0 : SSet.{u}) X =
      (pre spanSquareBoundary).app X := by
  dsimp only [squareCoconeFunctorIso, coconeRestriction]
  rw [← NatTrans.comp_app, ← pre_map]
  rfl

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
def squareFixedSpanCoconeIso {X : SSet.{u}} (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    vertexFiber ((pre spanSquareBoundary).app X) (functorVertex p) ≅ coconeFamily p :=
  SerrePositivity.InfinityCategories.F1B.vertexFiberSquareIso ((pre spanSquareBoundary).app X)
    (coconeRestriction (horn 2 0 : SSet.{u}) X) (squareCoconeFunctorIso X) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id] using
      (squareCoconeFunctorIso_restriction X).symm) (functorVertex p)
end SerrePositivity.InfinityCategories
