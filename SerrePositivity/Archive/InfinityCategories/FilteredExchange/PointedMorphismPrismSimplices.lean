module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.MorphismInitialHeadCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ReverseCompositionInitialHom

/-!
概要：同じ固定射の元の二つの実 prism の全単体を、同じ係数で束ねる。
方針：検証済みの実座標の右辺をそのまま使い、元の全対象の一致を保持する。
規約：単体を選び直さない。使われ方：Hom ごとの照合から実 prism 全体の一致へ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
variable (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
variable (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌)

/-- 元の全係数の pointed prism の、元の同じ全単体座標。 -/
def pointedMorphismSourceSimplex : SpaceInfinity.{u} _⦋n + 1⦌ :=
  coneInitialFixedSimplex pointKanObject (morphismInitialTail f (stdSimplex.objEquiv t))
    (SSet.yonedaEquiv.symm p)

/-- 元の全反転合成 prism の、元の同じ全単体座標。 -/
def pointedMorphismReverseSimplex : SpaceInfinity.{u} _⦋n + 1⦌ :=
  coherentOppositeInverseSimplex
    (coherentCompositionSimplex (X := Opposite.op L) (Y := Opposite.op K)
      (Z := Opposite.op pointKanObject) (PinchedHom.constant (functorVertex f) n)
      (SSet.opObjEquiv p) (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom))

/-- 同じ元の二単体表示の実対象の指定同定。 -/
lemma pointedMorphismSimplex_obj (a : Fin (n + 2)) :
    (pointedMorphismReverseSimplex f t p).obj ⟨ULift.up a⟩ =
      (pointedMorphismSourceSimplex f t p).obj ⟨ULift.up a⟩ :=
  congrArg Opposite.unop (pointedMorphismPrism_obj f t p a)

/-- 元の零時刻の正頂点は元の始域対象。 -/
lemma pointedMorphismSourceSimplex_obj_zero (j : Fin (n + 1))
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 0) :
    (pointedMorphismSourceSimplex f t p).obj ⟨ULift.up j.succ⟩ = K :=
  morphismInitialTail_obj_zero f (stdSimplex.objEquiv t) j hj

/-- 元の一時刻の正頂点は元の終域対象。 -/
lemma pointedMorphismSourceSimplex_obj_one (j : Fin (n + 1))
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 1) :
    (pointedMorphismSourceSimplex f t p).obj ⟨ULift.up j.succ⟩ = L :=
  morphismInitialTail_obj_one f (stdSimplex.objEquiv t) j hj

end SerrePositivity.InfinityCategories.F2
