module

public import SerrePositivity.KST.LocalizingInvariants.SquareFrameBoundary
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalBoundaryExt
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalBoundaryPostcomposition
public import SerrePositivity.InfinityCategories.Core.CommutativeSquareRealization

/-!
概要：正方形の境界図式の四辺と、後合成・元の正方形への制限を保持する。
方針：積の和の両側と区間境界の二端点で検査する。
規約：境界図式の選び直しをしない。使われ方：四辺の変形を元の全図式へ延長する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareFrame
variable {X Y : SSet.{u}} (f : SquareFrame X)

def postcomp (F : X ⟶ Y) : SquareFrame Y where
  bottom := f.bottom ≫ F
  top := f.top ≫ F
  left := f.left ≫ F
  right := f.right ≫ F
  lower_left := by simpa only [Category.assoc] using congrArg (· ≫ F) f.lower_left
  lower_right := by simpa only [Category.assoc] using congrArg (· ≫ F) f.lower_right
  upper_left := by simpa only [Category.assoc] using congrArg (· ≫ F) f.upper_left
  upper_right := by simpa only [Category.assoc] using congrArg (· ≫ F) f.upper_right

lemma diagram_postcomp (F : X ⟶ Y) : f.diagram ≫ F = (f.postcomp F).diagram := by
  apply (Subcomplex.unionProd.isPushout (SSet.boundary 1) (SSet.boundary 1)).hom_ext
  · rw [← Category.assoc, diagram_horizontal, diagram_horizontal]
    exact congrArg ((β_ _ _).hom ≫ ·)
      (F2.intervalBoundaryDiagram_postcomp f.bottom f.top F)
  · rw [← Category.assoc, diagram_vertical, diagram_vertical]
    exact F2.intervalBoundaryDiagram_postcomp f.left f.right F

def ofSquare (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : SquareFrame X where
  bottom := squareBottomEdge ≫ Q
  top := squareTopEdge ≫ Q
  left := squareLeftEdge ≫ Q
  right := squareRightEdge ≫ Q
  lower_left := by
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (· ≫ Q)
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  lower_right := by
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (· ≫ Q)
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  upper_left := by
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (· ≫ Q)
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  upper_right := by
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (· ≫ Q)
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

lemma diagram_ofSquare (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    (ofSquare Q).diagram = boundaryι ≫ Q := by
  apply (Subcomplex.unionProd.isPushout (SSet.boundary 1) (SSet.boundary 1)).hom_ext
  · rw [diagram_horizontal, ← Category.assoc, boundaryι, Subcomplex.unionProd.ι₁_ι]
    have he := F2.intervalBoundaryDiagram_eta
      ((((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[1] Δ[1]).hom) ≫ Q)
    change (((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
      (β_ Δ[1] Δ[1]).hom) ≫ Q = intervalBoundaryDiagram
        (squareBottomEdge ≫ Q) (squareTopEdge ≫ Q) at he
    have hb : (β_ (Δ[1] : SSet.{u}) (SSet.boundary 1 : SSet.{u})).hom ≫
        (((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[1] Δ[1]).hom) =
          (Δ[1] : SSet.{u}) ◁ (SSet.boundary 1).ι := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      rintro ⟨x, s⟩
      rfl
    calc
      _ = (β_ _ _).hom ≫ intervalBoundaryDiagram
          (squareBottomEdge ≫ Q) (squareTopEdge ≫ Q) := rfl
      _ = (β_ _ _).hom ≫
          ((((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[1] Δ[1]).hom) ≫ Q) :=
        congrArg (_ ≫ ·) he.symm
      _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Q) hb)
  · rw [diagram_vertical, ← Category.assoc, boundaryι, Subcomplex.unionProd.ι₂_ι]
    have hl : squareLeftEdge = prismEndpoint 0 (Δ[1] : SSet.{u}) := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    have hr : squareRightEdge = prismEndpoint 1 (Δ[1] : SSet.{u}) := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    change intervalBoundaryDiagram (squareLeftEdge ≫ Q) (squareRightEdge ≫ Q) = _
    rw [hl, hr]
    simpa only [← Category.assoc, intervalBoundaryEndpoint_ι] using
      (F2.intervalBoundaryDiagram_eta (((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ Q)).symm

def horizontalEndpoint (i : Fin 2) : (Δ[1] : SSet.{u}) ⟶ boundary.{u} :=
  intervalBoundaryEndpoint i Δ[1] ≫ (β_ _ _).hom ≫
    Subcomplex.unionProd.ι₁ (SSet.boundary 1) (SSet.boundary 1)

def verticalEndpoint (i : Fin 2) : (Δ[1] : SSet.{u}) ⟶ boundary.{u} :=
  intervalBoundaryEndpoint i Δ[1] ≫
    Subcomplex.unionProd.ι₂ (SSet.boundary 1) (SSet.boundary 1)

lemma diagram_bottom : horizontalEndpoint 0 ≫ f.diagram = f.bottom := by
  rw [horizontalEndpoint, Category.assoc, Category.assoc, diagram_horizontal]
  change intervalBoundaryEndpoint 0 _ ≫ intervalBoundaryDiagram f.bottom f.top = _
  exact intervalBoundaryDiagram_zero _ _

lemma diagram_top : horizontalEndpoint 1 ≫ f.diagram = f.top := by
  rw [horizontalEndpoint, Category.assoc, Category.assoc, diagram_horizontal]
  change intervalBoundaryEndpoint 1 _ ≫ intervalBoundaryDiagram f.bottom f.top = _
  exact intervalBoundaryDiagram_one _ _

lemma diagram_left : verticalEndpoint 0 ≫ f.diagram = f.left := by
  rw [verticalEndpoint, Category.assoc, diagram_vertical]
  exact intervalBoundaryDiagram_zero _ _

lemma diagram_right : verticalEndpoint 1 ≫ f.diagram = f.right := by
  rw [verticalEndpoint, Category.assoc, diagram_vertical]
  exact intervalBoundaryDiagram_one _ _

lemma horizontalEndpoint_zero_ι : horizontalEndpoint 0 ≫ boundaryι.{u} = squareBottomEdge := by
  rw [horizontalEndpoint, boundaryι, Category.assoc, Category.assoc,
    Subcomplex.unionProd.ι₁_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma horizontalEndpoint_one_ι : horizontalEndpoint 1 ≫ boundaryι.{u} = squareTopEdge := by
  rw [horizontalEndpoint, boundaryι, Category.assoc, Category.assoc,
    Subcomplex.unionProd.ι₁_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma verticalEndpoint_zero_ι : verticalEndpoint 0 ≫ boundaryι.{u} = squareLeftEdge := by
  rw [verticalEndpoint, boundaryι, Category.assoc, Subcomplex.unionProd.ι₂_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma verticalEndpoint_one_ι : verticalEndpoint 1 ≫ boundaryι.{u} = squareRightEdge := by
  rw [verticalEndpoint, boundaryι, Category.assoc, Subcomplex.unionProd.ι₂_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma square_bottom_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : boundaryι ≫ Q = f.diagram) : squareBottomEdge ≫ Q = f.bottom := by
  have he := congrArg (horizontalEndpoint 0 ≫ ·) h
  rw [← Category.assoc, horizontalEndpoint_zero_ι, diagram_bottom] at he
  exact he

lemma square_top_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : boundaryι ≫ Q = f.diagram) : squareTopEdge ≫ Q = f.top := by
  have he := congrArg (horizontalEndpoint 1 ≫ ·) h
  rw [← Category.assoc, horizontalEndpoint_one_ι, diagram_top] at he
  exact he

lemma square_left_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : boundaryι ≫ Q = f.diagram) : squareLeftEdge ≫ Q = f.left := by
  have he := congrArg (verticalEndpoint 0 ≫ ·) h
  rw [← Category.assoc, verticalEndpoint_zero_ι, diagram_left] at he
  exact he

lemma square_right_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : boundaryι ≫ Q = f.diagram) : squareRightEdge ≫ Q = f.right := by
  have he := congrArg (verticalEndpoint 1 ≫ ·) h
  rw [← Category.assoc, verticalEndpoint_one_ι, diagram_right] at he
  exact he

end SerrePositivity.KST.LocalizingInvariants.SquareFrame
