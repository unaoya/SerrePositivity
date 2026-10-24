module
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareFixedSpanInitial
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberBaseChange

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
def zeroCornerSquareSpanPullbackIso (X : SSet.{u}) : zeroCornerSquares X ≅
    pullback ((pre spanSquareBoundary).app X)
      (fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
        IsZeroOuterSpanVertex).ι := by
  let P := fun v ↦ IsZeroOuterSpanVertex
    (((pre spanSquareBoundary).app X).app (Opposite.op ⦋0⦌) v)
  refine fullSubcomplexIso (Iso.refl _) IsZeroCornerSquareVertex P ?_ ≪≫
    coneInputFullSubcomplexIso _ _
  intro v
  exact (zeroOuterSpanVertex_square_iff v).symm

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma zeroCornerSquareSpanPullbackIso_diagram (X : SSet.{u}) :
    (zeroCornerSquareSpanPullbackIso X).hom ≫
      pullback.fst ((pre spanSquareBoundary).app X)
        (fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
          IsZeroOuterSpanVertex).ι =
      (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
        IsZeroCornerSquareVertex).ι := by
  dsimp only [zeroCornerSquareSpanPullbackIso, Iso.trans_hom]
  rw [Category.assoc, coneInputFullSubcomplexIso_hom_fst, fullSubcomplexIso_hom_ι]
  exact Category.comp_id _

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma zeroCornerSquareSpanPullbackIso_span (X : SSet.{u}) :
    (zeroCornerSquareSpanPullbackIso X).hom ≫
      pullback.snd ((pre spanSquareBoundary).app X)
        (fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
          IsZeroOuterSpanVertex).ι = zeroCornerSquareSpan X := by
  apply (cancel_mono (fullSubcomplexOnVertices _ IsZeroOuterSpanVertex).ι).1
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    zeroCornerSquareSpanPullbackIso_diagram]
  exact (fullSubcomplexLift_ι _ _ _).symm

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
def zeroCornerSquareFixedSpanRawIso (X : SSet.{u}) (b : (zeroOuterSpans X) _⦋0⦌) :
    vertexFiber (zeroCornerSquareSpan X) b ≅
      vertexFiber ((pre spanSquareBoundary).app X) b.val := by
  let q := pullback.snd ((pre spanSquareBoundary).app X)
    (fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
      IsZeroOuterSpanVertex).ι
  let f := vertexFiberMap (zeroCornerSquareSpan X) q
    (zeroCornerSquareSpanPullbackIso X).hom (zeroCornerSquareSpanPullbackIso_span X) b
  have : IsIso f := HomotopyLimits.vertexFiberMap_isIso _ _ _ _ _
  exact asIso f ≪≫ cofinalVertexFiberBaseChangeIso ((pre spanSquareBoundary).app X)
    (fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
      IsZeroOuterSpanVertex).ι b
end SerrePositivity.InfinityCategories
