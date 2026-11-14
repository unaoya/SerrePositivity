module

public import SerrePositivity.KST.LocalizingInvariants.BinarySecondProjection
public import SerrePositivity.KST.LocalizingInvariants.HorizontalEquivalencePullback
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomClass
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PullbackPasting

/-!
概要：元の BF graph と対角を四辺に持つ正方形を構成する。
方針：厳密な積射の可換性を実現し、第二射影の基底変換へ貼り合わせる準備をする。
規約：元の BF 射と合成三角形を保持。使われ方：対角から二脚の pullback への変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryGraph
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (A B : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom A B) :=
  OmegaSpectrum.mappingSpace_kanComplex A B
variable {Y Z : OmegaSpectrum.{u}} (g : Y ⟶ Z)

def graph : Y ⟶ Binary.obj Z Y := Binary.lift g (𝟙 Y)
def diagonal (Z : OmegaSpectrum.{u}) : Z ⟶ Binary.obj Z Z := Binary.lift (𝟙 Z) (𝟙 Z)

lemma condition : graph g ≫ Binary.map (𝟙 Z) g = g ≫ diagonal Z := by
  apply Binary.lift_ext <;> simp [graph, diagonal, Category.assoc]

lemma exists_square : ∃ s : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u},
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (graph g)).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ s = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (diagonal Z)).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ s = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ s =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map (𝟙 Z) g)).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm (X := Sp.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (graph g)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (diagonal Z)).toTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map (𝟙 Z) g)).toTruncated
  change SpectrumHo.hom (graph g) ≫ SpectrumHo.hom (Binary.map (𝟙 Z) g) =
    SpectrumHo.hom g ≫ SpectrumHo.hom (diagonal Z)
  rw [← SpectrumHo.hom_comp, ← SpectrumHo.hom_comp, condition]

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (exists_square g).choose

lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square g =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (graph g)).edge := (exists_square g).choose_spec.1

lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square g =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (diagonal Z)).edge :=
  (exists_square g).choose_spec.2.1

lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square g =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge := (exists_square g).choose_spec.2.2.1

lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square g =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map (𝟙 Z) g)).edge :=
  (exists_square g).choose_spec.2.2.2

def bottomComposition : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (graph g))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.snd Z Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 Y)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (graph g) (Binary.snd Z Y)).ofEq rfl rfl
    (by rw [graph, Binary.lift_snd])

def topComposition (Z : OmegaSpectrum.{u}) : SSet.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (diagonal Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.snd Z Z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 Z)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (diagonal Z) (Binary.snd Z Z)).ofEq rfl rfl
    (by rw [diagonal, Binary.lift_snd])

def rectangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle (square g) (BinarySecondProjection.square g Z)
    (SSet.yonedaEquiv.symm (bottomComposition g).simplex)
    (SSet.yonedaEquiv.symm (topComposition Z).simplex) := by
  apply Classical.choice
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.nonempty_squarePastingRectangle
  · rw [square_right, BinarySecondProjection.square_left]
  · rw [square_bottom, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (bottomComposition g).d₂.symm
  · rw [BinarySecondProjection.square_bottom, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (bottomComposition g).d₀.symm
  · rw [square_top, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (topComposition Z).d₂.symm
  · rw [BinarySecondProjection.square_top, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (topComposition Z).d₀.symm

end SerrePositivity.KST.LocalizingInvariants.BinaryGraph
