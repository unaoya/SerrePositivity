module

public import SerrePositivity.KST.LocalizingInvariants.CompositionDiagonalTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization

/-!
概要：指定された比較三角形を保つ四辺固定の正方形。
方針：比較三角形に沿って下三角形の対角を移送し、上三角形と貼る。
規約：元の三次元充填の証人と両三角形を保持。使われ方：不変量へ写す元の正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.PathComparisonSquare
variable {X : SSet.{u}} [Quasicategory X] {x y x' z : X _⦋0⦌}
  {f : X.Edge x y} {g : X.Edge y z} {a : X.Edge x x'} {b : X.Edge x' z}
  {k k' : X.Edge x z} (s : SSet.Edge.CompStruct f g k) (t : SSet.Edge.CompStruct a b k')
  (H : SSet.Edge.CompStruct (SSet.Edge.id x) k k')

lemma diagonal_eq : stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
    stdSimplex.δ (1 : Fin 3) ≫
      SSet.yonedaEquiv.symm (compositionDiagonalTransport s H).triangle.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
    t.d₁, (compositionDiagonalTransport s H).triangle.d₁]

def square : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm t.simplex)
    (SSet.yonedaEquiv.symm (compositionDiagonalTransport s H).triangle.simplex)
    (diagonal_eq s t H)

lemma square_upper : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ square s t H = SSet.yonedaEquiv.symm t.simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

lemma square_lower : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ square s t H =
    SSet.yonedaEquiv.symm (compositionDiagonalTransport s H).triangle.simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square s t H = SSet.yonedaEquiv.symm f.edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge, Category.assoc, square_lower,
    stdSimplex.δ_comp_yonedaEquiv_symm, (compositionDiagonalTransport s H).triangle.d₂]

lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square s t H = SSet.yonedaEquiv.symm g.edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, square_lower,
    stdSimplex.δ_comp_yonedaEquiv_symm, (compositionDiagonalTransport s H).triangle.d₀]

lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square s t H = SSet.yonedaEquiv.symm a.edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge, Category.assoc, square_upper,
    stdSimplex.δ_comp_yonedaEquiv_symm, t.d₂]

lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square s t H = SSet.yonedaEquiv.symm b.edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge, Category.assoc, square_upper,
    stdSimplex.δ_comp_yonedaEquiv_symm, t.d₀]

end SerrePositivity.KST.LocalizingInvariants.PathComparisonSquare
