module

public import SerrePositivity.KST.LocalizingInvariants.BinaryProjectionCone
public import SerrePositivity.KST.LocalizingInvariants.StrictCospanConeLegs
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareTransposeEdges
public import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality

/-!
概要：元の BF 積の射影を基底変換する、四辺を厳密に保持した実 pullback 正方形。
方針：各段の積から得た実極限錐を正方形へ戻して転置する。
規約：下辺は元の第一射影、左辺は f×id。使われ方：d8 の積から二脚への貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryProjection
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z) (Y : OmegaSpectrum.{u})

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    StrictCospanCone.square (Binary.fst Z Y) f (cone f Y)

lemma square_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (square f Y) :=
  (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose _).mp
    (StrictCospanCone.square_isPullback _ _ _ (infinityCone_isLimit f Y))

lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square f Y =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.fst X Y)).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom, StrictCospanCone.square_left]
  rfl

lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square f Y =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map f (𝟙 Y))).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_left, StrictCospanCone.square_bottom]
  rfl

lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square f Y =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_right, StrictCospanCone.square_top]

lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square f Y =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.fst Z Y)).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_top, StrictCospanCone.square_right]

lemma square_vertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (square f Y) 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj X Y) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (StrictCospanCone.square (Binary.fst Z Y) f (cone f Y)) 0 0 = _
  exact StrictCospanCone.square_vertex _ _ _

end SerrePositivity.KST.LocalizingInvariants.BinaryProjection
