module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrameBoundary
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareFrame
end SerrePositivity.KST.LocalizingInvariants.SquareFrame
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.SquareFrame
variable {X Y : SSet.{u}} (f : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame X)

def postcomp (F : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame Y where
  bottom := f.bottom ≫ F
  top := f.top ≫ F
  left := f.left ≫ F
  right := f.right ≫ F
  lower_left := by simpa only [Category.assoc] using congrArg (· ≫ F) f.lower_left
  lower_right := by simpa only [Category.assoc] using congrArg (· ≫ F) f.lower_right
  upper_left := by simpa only [Category.assoc] using congrArg (· ≫ F) f.upper_left
  upper_right := by simpa only [Category.assoc] using congrArg (· ≫ F) f.upper_right

lemma diagram_postcomp (F : X ⟶ Y) : f.diagram ≫ F = ((postcomp f) F).diagram := by
  apply (Subcomplex.unionProd.isPushout (SSet.boundary 1) (SSet.boundary 1)).hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_horizontal, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_horizontal]
    exact congrArg ((β_ _ _).hom ≫ ·)
      (F2.intervalBoundaryDiagram_postcomp f.bottom f.top F)
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_vertical, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_vertical]
    exact F2.intervalBoundaryDiagram_postcomp f.left f.right F

def ofSquare (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame X where
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
    (ofSquare Q).diagram = _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ Q := by
  apply (Subcomplex.unionProd.isPushout (SSet.boundary 1) (SSet.boundary 1)).hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_horizontal, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι, Subcomplex.unionProd.ι₁_ι]
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
  · rw [_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_vertical, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι, Subcomplex.unionProd.ι₂_ι]
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

def horizontalEndpoint (i : Fin 2) : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundary.{u} :=
  intervalBoundaryEndpoint i Δ[1] ≫ (β_ _ _).hom ≫
    Subcomplex.unionProd.ι₁ (SSet.boundary 1) (SSet.boundary 1)

def verticalEndpoint (i : Fin 2) : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundary.{u} :=
  intervalBoundaryEndpoint i Δ[1] ≫
    Subcomplex.unionProd.ι₂ (SSet.boundary 1) (SSet.boundary 1)

lemma diagram_bottom : horizontalEndpoint 0 ≫ f.diagram = f.bottom := by
  rw [horizontalEndpoint, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_horizontal]
  change intervalBoundaryEndpoint 0 _ ≫ intervalBoundaryDiagram f.bottom f.top = _
  exact intervalBoundaryDiagram_zero _ _

lemma diagram_top : horizontalEndpoint 1 ≫ f.diagram = f.top := by
  rw [horizontalEndpoint, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_horizontal]
  change intervalBoundaryEndpoint 1 _ ≫ intervalBoundaryDiagram f.bottom f.top = _
  exact intervalBoundaryDiagram_one _ _

lemma diagram_left : verticalEndpoint 0 ≫ f.diagram = f.left := by
  rw [verticalEndpoint, Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_vertical]
  exact intervalBoundaryDiagram_zero _ _

lemma diagram_right : verticalEndpoint 1 ≫ f.diagram = f.right := by
  rw [verticalEndpoint, Category.assoc, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.diagram_vertical]
  exact intervalBoundaryDiagram_one _ _

lemma horizontalEndpoint_zero_ι : horizontalEndpoint 0 ≫ _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι.{u} = squareBottomEdge := by
  rw [horizontalEndpoint, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι, Category.assoc, Category.assoc,
    Subcomplex.unionProd.ι₁_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma horizontalEndpoint_one_ι : horizontalEndpoint 1 ≫ _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι.{u} = squareTopEdge := by
  rw [horizontalEndpoint, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι, Category.assoc, Category.assoc,
    Subcomplex.unionProd.ι₁_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma verticalEndpoint_zero_ι : verticalEndpoint 0 ≫ _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι.{u} = squareLeftEdge := by
  rw [verticalEndpoint, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι, Category.assoc, Subcomplex.unionProd.ι₂_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma verticalEndpoint_one_ι : verticalEndpoint 1 ≫ _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι.{u} = squareRightEdge := by
  rw [verticalEndpoint, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι, Category.assoc, Subcomplex.unionProd.ι₂_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma square_bottom_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ Q = f.diagram) : squareBottomEdge ≫ Q = f.bottom := by
  have he := congrArg (horizontalEndpoint 0 ≫ ·) h
  rw [← Category.assoc, horizontalEndpoint_zero_ι, diagram_bottom] at he
  exact he

lemma square_top_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ Q = f.diagram) : squareTopEdge ≫ Q = f.top := by
  have he := congrArg (horizontalEndpoint 1 ≫ ·) h
  rw [← Category.assoc, horizontalEndpoint_one_ι, diagram_top] at he
  exact he

lemma square_left_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ Q = f.diagram) : squareLeftEdge ≫ Q = f.left := by
  have he := congrArg (verticalEndpoint 0 ≫ ·) h
  rw [← Category.assoc, verticalEndpoint_zero_ι, diagram_left] at he
  exact he

lemma square_right_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ Q = f.diagram) : squareRightEdge ≫ Q = f.right := by
  have he := congrArg (verticalEndpoint 1 ≫ ·) h
  rw [← Category.assoc, verticalEndpoint_one_ι, diagram_right] at he
  exact he

end SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram_bottom := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram_left := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram_ofSquare := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_ofSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram_postcomp := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_postcomp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram_right := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram_top := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_top

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.horizontalEndpoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.horizontalEndpoint := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.horizontalEndpoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.horizontalEndpoint_one_ι := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.horizontalEndpoint_one_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.horizontalEndpoint_zero_ι := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.horizontalEndpoint_zero_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.ofSquare := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.postcomp := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.square_bottom_of_boundary := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_bottom_of_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.square_left_of_boundary := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_left_of_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.square_right_of_boundary := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_right_of_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.square_top_of_boundary := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_top_of_boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.verticalEndpoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.verticalEndpoint := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.verticalEndpoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.verticalEndpoint_one_ι := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.verticalEndpoint_one_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.verticalEndpoint_zero_ι := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.verticalEndpoint_zero_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.horizontalEndpoint.eq_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.horizontalEndpoint.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.ofSquare._proof_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.ofSquare._proof_2 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.ofSquare._proof_3 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.ofSquare._proof_4 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.postcomp._proof_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.postcomp._proof_2 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.postcomp._proof_3 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.postcomp._proof_4 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.verticalEndpoint.eq_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.verticalEndpoint.eq_1
