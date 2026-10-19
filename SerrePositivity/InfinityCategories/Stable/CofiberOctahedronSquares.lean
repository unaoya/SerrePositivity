module
public import SerrePositivity.InfinityCategories.Stable.CofiberOctahedronDiagram

/-! # 実八面体の三つの cofiber 四角形

概要：合成二単体の三辺の cofiber と、それらを結ぶ列の頂点を厳密に照合する。
方針：二つの長方形の底辺・左面の等式を使う。
規約：cofiber の選択を変更しない。使われ方：Verdier 分母の二対三性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {X : SSet.{u}} {t : ZeroTriangle X} {τ : Δ[2] ⟶ X}

/-- 長辺の実 cofiber 四角形。 -/
def CofiberOctahedronDiagram.compositeCofiberSquare (d : CofiberOctahedronDiagram t τ) :
    CofiberSquare (edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ τ))) where
  toZeroTriangle := d.first.outerZeroTriangle
  bottom_edge := by
    change squareBottomEdge ≫ d.first.outerZeroTriangle.square =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ τ))
    rw [SSet.yonedaEquiv.symm_apply_apply]
    exact (pastingSquare_bottomEdge d.first.diagram 1).trans
      (congrArg (fun q => stdSimplex.δ (1 : Fin 3) ≫ q) d.first.bottom_eq)
  isPushout := d.first.outer_isCofiber

/-- 第二の短辺の実 cofiber 四角形。 -/
def CofiberOctahedronDiagram.nextCofiberSquare (d : CofiberOctahedronDiagram t τ) :
    CofiberSquare (edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ τ))) where
  toZeroTriangle := d.second.outerZeroTriangle
  bottom_edge := by
    change squareBottomEdge ≫ d.second.outerZeroTriangle.square =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ τ))
    rw [SSet.yonedaEquiv.symm_apply_apply, d.next_firstEdge,
      pastingSquare_bottomEdge, d.first.bottom_eq]
  isPushout := d.second.outer_isCofiber

/-- 最後の列の始点は最初の cofiber。 -/
lemma CofiberOctahedronDiagram.last_source (d : CofiberOctahedronDiagram t τ) :
    squareVertex d.second.rightZeroTriangle.square 0 0 = squareVertex t.square 1 1 := by
  have hv : squareVertex d.second.rightZeroTriangle.square 0 0 =
      squareVertex (pastingSquare d.second.diagram 2) 1 0 := rfl
  rw [hv, d.second.left_eq]
  change squareVertex (pastingSquare d.first.diagram 2) 1 1 = _
  rw [d.first.left_eq]

/-- 最後の列の中間頂点は合成射の cofiber。 -/
lemma CofiberOctahedronDiagram.last_middle (d : CofiberOctahedronDiagram t τ) :
    squareVertex d.second.rightZeroTriangle.square 1 0 =
      d.compositeCofiberSquare.cofiber := by
  have hv : squareVertex d.second.rightZeroTriangle.square 1 0 =
      squareVertex (pastingSquare d.second.diagram 2) 1 1 := rfl
  rw [hv, d.second.left_eq]
  rfl

/-- 最後の列の終点は第二の短辺の cofiber。 -/
lemma CofiberOctahedronDiagram.last_target (d : CofiberOctahedronDiagram t τ) :
    squareVertex d.second.rightZeroTriangle.square 1 1 = d.nextCofiberSquare.cofiber := rfl

end SerrePositivity.InfinityCategories
