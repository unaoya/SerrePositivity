module

public import SerrePositivity.KST.LocalizingInvariants.BinaryGraphPullback
public import SerrePositivity.KST.LocalizingInvariants.SpectrumProductIso

/-!
概要：可換な二脚から graph 正方形の左に付ける予備正方形を構成する。
方針：実積の二射影で射の類を比較し、四辺を固定して可換正方形を実現する。
規約：この段階では極限性を主張しない。使われ方：外周極限錐を保つ長方形への延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryGraphPreliminary
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (A B : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom A B) :=
  OmegaSpectrum.mappingSpace_kanComplex A B
variable {T X Y Z : OmegaSpectrum.{u}} (a : T ⟶ X) (b : T ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  (hc : SpectrumHo.hom a ≫ SpectrumHo.hom f = SpectrumHo.hom b ≫ SpectrumHo.hom g)

include hc in
lemma graph_comm : SpectrumHo.hom b ≫ SpectrumHo.hom (BinaryGraph.graph g) =
    SpectrumHo.hom (Binary.lift a b) ≫ SpectrumHo.hom (Binary.map f (𝟙 Y)) := by
  apply Binary.ho_hom_ext
  · simpa only [← SpectrumHo.hom_comp, Category.assoc, BinaryGraph.graph,
      Binary.lift_fst_assoc, Binary.lift_fst, Binary.map_fst, Category.comp_id] using
      hc.symm
  · simp only [← SpectrumHo.hom_comp, Category.assoc, BinaryGraph.graph,
      Binary.lift_snd, Binary.map_snd, Category.comp_id]

include hc in
lemma exists_square : ∃ s : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u},
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge b).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ s =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map f (𝟙 Y))).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ s = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.lift a b)).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ s = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (BinaryGraph.graph g)).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm (X := Sp.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge b).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map f (𝟙 Y))).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.lift a b)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (BinaryGraph.graph g)).toTruncated (graph_comm a b f g hc)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (exists_square a b f g hc).choose

lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square a b f g hc =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge b).edge := (exists_square a b f g hc).choose_spec.1

lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square a b f g hc =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map f (𝟙 Y))).edge :=
  (exists_square a b f g hc).choose_spec.2.1

lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square a b f g hc =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.lift a b)).edge :=
  (exists_square a b f g hc).choose_spec.2.2.1

lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square a b f g hc =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (BinaryGraph.graph g)).edge :=
  (exists_square a b f g hc).choose_spec.2.2.2

end SerrePositivity.KST.LocalizingInvariants.BinaryGraphPreliminary
