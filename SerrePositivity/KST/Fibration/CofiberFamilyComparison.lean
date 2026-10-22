module
public import SerrePositivity.KST.Fibration.CofiberFamilyTranspose
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso

/-! # 同じ実底辺を持つ cofiber 族の図式全体の比較

零角を持つ二つの実 cofiber 四角形を、共通の指定辺の cofiber として比較する。
関手圏に適用すれば、比較は全パラメーターを持つ自然同型となる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 実底辺が等しい二つの cofiber 族の図式全体は自然同型である。 -/
def cofiberFamilyComparison {X : SSet.{u}} [Quasicategory X]
    (t s : ZeroTriangle X) (ht : IsCofiberSequence t) (hs : IsCofiberSequence s)
    (h : squareBottomEdge ≫ t.square = squareBottomEdge ≫ s.square) :
    FunctorIso t.square s.square := by
  let f := squareBottomArrow t.square
  have hb : squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm f.edge :=
    (SSet.yonedaEquiv.symm_apply_apply _).symm.trans
      (congrArg SSet.yonedaEquiv.symm (squareBottomArrow_edge t.square).symm)
  let ct : CofiberSquare f := ⟨t, hb, ht⟩
  let cs : CofiberSquare f := ⟨s, h.symm.trans hb, hs⟩
  exact Classical.choice (nonempty_cofiberSquareFunctorIso ct cs)

/-- 実四角形の全図式の同型を、その cofiber 頂点で評価する。 -/
def cofiberFamilyCornerIso {X : SSet.{u}} [Quasicategory X]
    {t s : ZeroTriangle X} (e : FunctorIso t.square s.square) :
    VertexIso (squareVertex t.square 1 1) (squareVertex s.square 1 1) := by
  have he := VertexIso.map e (evaluateFunctorAt (Y := X)
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1))
  simpa only [evaluateFunctorAt_functorVertex, squareVertex] using he

end SerrePositivity.KST.Fibration
