module


public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrameBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalBoundaryExt
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalBoundaryPostcomposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization

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
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} (f : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame X)

def postcomp (F : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame Y where
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
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_horizontal, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_horizontal]
    exact congrArg ((β_ _ _).hom ≫ ·)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryDiagram_postcomp f.bottom f.top F)
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_vertical, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_vertical]
    exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryDiagram_postcomp f.left f.right F

def ofSquare (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame X where
  bottom := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q
  top := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q
  left := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ Q
  right := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q
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
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare Q).diagram = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ Q := by
  apply (Subcomplex.unionProd.isPushout (SSet.boundary 1) (SSet.boundary 1)).hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_horizontal, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι, Subcomplex.unionProd.ι₁_ι]
    have he := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryDiagram_eta
      ((((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[1] Δ[1]).hom) ≫ Q)
    change (((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
      (β_ Δ[1] Δ[1]).hom) ≫ Q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q) at he
    have hb : (β_ (Δ[1] : SSet.{u}) (SSet.boundary 1 : SSet.{u})).hom ≫
        (((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[1] Δ[1]).hom) =
          (Δ[1] : SSet.{u}) ◁ (SSet.boundary 1).ι := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      rintro ⟨x, s⟩
      rfl
    calc
      _ = (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q) := rfl
      _ = (β_ _ _).hom ≫
          ((((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[1] Δ[1]).hom) ≫ Q) :=
        congrArg (_ ≫ ·) he.symm
      _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Q) hb)
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_vertical, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι, Subcomplex.unionProd.ι₂_ι]
    have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q) = _
    rw [hl, hr]
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι] using
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryDiagram_eta (((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ Q)).symm

def horizontalEndpoint (i : Fin 2) : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundary.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint i Δ[1] ≫ (β_ _ _).hom ≫
    Subcomplex.unionProd.ι₁ (SSet.boundary 1) (SSet.boundary 1)

def verticalEndpoint (i : Fin 2) : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundary.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint i Δ[1] ≫
    Subcomplex.unionProd.ι₂ (SSet.boundary 1) (SSet.boundary 1)

lemma diagram_bottom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint 0 ≫ f.diagram = f.bottom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_horizontal]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f.bottom f.top = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero _ _

lemma diagram_top : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint 1 ≫ f.diagram = f.top := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_horizontal]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f.bottom f.top = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one _ _

lemma diagram_left : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint 0 ≫ f.diagram = f.left := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_vertical]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero _ _

lemma diagram_right : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint 1 ≫ f.diagram = f.right := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_vertical]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one _ _

lemma horizontalEndpoint_zero_ι : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι, Category.assoc, Category.assoc,
    Subcomplex.unionProd.ι₁_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma horizontalEndpoint_one_ι : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι, Category.assoc, Category.assoc,
    Subcomplex.unionProd.ι₁_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma verticalEndpoint_zero_ι : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι, Category.assoc, Subcomplex.unionProd.ι₂_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma verticalEndpoint_one_ι : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι, Category.assoc, Subcomplex.unionProd.ι₂_ι]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma square_bottom_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ Q = f.diagram) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q = f.bottom := by
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint 0 ≫ ·) h
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint_zero_ι, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.diagram_bottom] at he
  exact he

lemma square_top_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ Q = f.diagram) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q = f.top := by
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint 1 ≫ ·) h
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.horizontalEndpoint_one_ι, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.diagram_top] at he
  exact he

lemma square_left_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ Q = f.diagram) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ Q = f.left := by
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint 0 ≫ ·) h
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint_zero_ι, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.diagram_left] at he
  exact he

lemma square_right_of_boundary {Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ Q = f.diagram) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q = f.right := by
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint 1 ≫ ·) h
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.verticalEndpoint_one_ι, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.diagram_right] at he
  exact he

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
