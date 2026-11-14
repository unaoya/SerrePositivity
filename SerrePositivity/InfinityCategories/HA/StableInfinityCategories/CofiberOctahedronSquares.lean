module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram

/-! # 実八面体の三つの cofiber 四角形

概要：合成二単体の三辺の cofiber と、それらを結ぶ列の頂点を厳密に照合する。
方針：二つの長方形の底辺・左面の等式を使う。
規約：cofiber の選択を変更しない。使われ方：Verdier 分母の二対三性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X} {τ : Δ[2] ⟶ X}

/-- 長辺の実 cofiber 四角形。 -/
def CofiberOctahedronDiagram.compositeCofiberSquare (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ τ))) where
  toZeroTriangle := d.first.outerZeroTriangle
  bottom_edge := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.first.outerZeroTriangle.square =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ τ))
    rw [SSet.yonedaEquiv.symm_apply_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge d.first.diagram 1).trans
      (congrArg (fun q => stdSimplex.δ (1 : Fin 3) ≫ q) d.first.bottom_eq)
  isPushout := d.first.outer_isCofiber

/-- 第二の短辺の実 cofiber 四角形。 -/
def CofiberOctahedronDiagram.nextCofiberSquare (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ τ))) where
  toZeroTriangle := d.second.outerZeroTriangle
  bottom_edge := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.second.outerZeroTriangle.square =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ τ))
    rw [SSet.yonedaEquiv.symm_apply_apply, d.next_firstEdge,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge, d.first.bottom_eq]
  isPushout := d.second.outer_isCofiber

/-- 最後の列の始点は最初の cofiber。 -/
lemma CofiberOctahedronDiagram.last_source (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.second.rightZeroTriangle.square 0 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1 := by
  have hv : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.second.rightZeroTriangle.square 0 0 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.second.diagram 2) 1 0 := rfl
  rw [hv, d.second.left_eq]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 2) 1 1 = _
  rw [d.first.left_eq]

/-- 最後の列の中間頂点は合成射の cofiber。 -/
lemma CofiberOctahedronDiagram.last_middle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.second.rightZeroTriangle.square 1 0 =
      d.compositeCofiberSquare.cofiber := by
  have hv : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.second.rightZeroTriangle.square 1 0 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.second.diagram 2) 1 1 := rfl
  rw [hv, d.second.left_eq]
  rfl

/-- 最後の列の終点は第二の短辺の cofiber。 -/
lemma CofiberOctahedronDiagram.last_target (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.second.rightZeroTriangle.square 1 1 = d.nextCofiberSquare.cofiber := rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
