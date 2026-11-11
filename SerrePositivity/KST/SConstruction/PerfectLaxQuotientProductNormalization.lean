module
public import SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquareFrameFunctoriality
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientValueCospan
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameEdgesHomotopy

/-! # 元の四つの実 BF 射を固定する正方形の境界変形
概要：元の実積正方形を、元の射対・対角・核の射・二脚の実積射の四辺へ移す。
方針：四辺の同じ射の類と端点から境界 homotopy を作り、全正方形へ延長する。
規約：同じ全図式の比較と引き戻し性を保持する。使われ方：二脚の実 pullback。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
local instance normalizedProductSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 元の下辺の端点を同じ BF 表示へ合わせた実辺。 -/
def productBottomEdge : Sp.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (perfectInvariantSpectrum F
  (perfectStableVertex d.left d.left_complete)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (perfectInvariantSpectrum F (perfectStableVertex C
      d.c_complete)) (perfectInvariantSpectrum F (perfectStableVertex D d.d_complete)))) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (d.productSquare hF))).ofEq
    (d.productSquare_vertex00 hF) (d.productSquare_vertex10 hF)

/-- 元の上辺の端点を同じ BF 表示へ合わせた実辺。 -/
def productTopEdge : Sp.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (perfectInvariantSpectrum F
  d.sequence.rightVertex))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (perfectInvariantSpectrum F d.sequence.rightVertex)
      (perfectInvariantSpectrum F d.sequence.rightVertex))) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (d.productSquare hF))).ofEq
    (d.productSquare_vertex01 hF) (d.productSquare_vertex11 hF)

/-- 元の左辺の端点を同じ BF 表示へ合わせた実辺。 -/
def productLeftEdge : Sp.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (perfectInvariantSpectrum F
  (perfectStableVertex d.left d.left_complete))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (perfectInvariantSpectrum
    F d.sequence.rightVertex)) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow (d.productSquare hF))).ofEq
    (d.productSquare_vertex00 hF) (d.productSquare_vertex01 hF)

/-- 元の右辺の端点を同じ BF 表示へ合わせた実辺。 -/
def productRightEdge : Sp.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (perfectInvariantSpectrum F
  (perfectStableVertex C d.c_complete)) (perfectInvariantSpectrum F (perfectStableVertex D
    d.d_complete))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (perfectInvariantSpectrum F d.sequence.rightVertex)
      (perfectInvariantSpectrum F d.sequence.rightVertex))) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (d.productSquare hF))).ofEq
    (d.productSquare_vertex10 hF) (d.productSquare_vertex11 hF)

/-- 元の同じ四辺を持つ実境界。 -/
def productOldFrame : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges (d.productBottomEdge hF)
  (d.productTopEdge hF) (d.productLeftEdge hF) (d.productRightEdge hF)

/-- 同じ四辺の境界は、元の正方形の境界そのもの。 -/
lemma productOldFrame_eq : d.productOldFrame hF =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (d.productSquare hF) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.ext
  · change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow _).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow _).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow _).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow _).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _

/-- 同じ下辺の類は、元の実 C・D 射対の積包含。 -/
lemma productBottomEdge_class : Truncated.HomotopyCategory.homMk (d.productBottomEdge
  hF).toTruncated =
    SpectrumHo.hom (d.valueProductInclusion F) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (d.productBottomEdge hF).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (d.productSquare hF)) rfl).trans
      (d.productSquare_bottom_native_arrow hF)

/-- 同じ上辺の類は、元の完備化先の値の実対角。 -/
lemma productTopEdge_class : Truncated.HomotopyCategory.homMk (d.productTopEdge hF).toTruncated =
    SpectrumHo.hom (Binary.lift (𝟙 (perfectInvariantSpectrum F d.sequence.rightVertex)) (𝟙
      (perfectInvariantSpectrum F d.sequence.rightVertex))) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (d.productTopEdge hF).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (d.productSquare hF)) rfl).trans
      (d.productSquare_top_arrow hF)

/-- 同じ左辺の類は、元の核の射の実 BF 値。 -/
lemma productLeftEdge_class : Truncated.HomotopyCategory.homMk (d.productLeftEdge hF).toTruncated =
    SpectrumHo.hom (d.valueKernelMap F) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (d.productLeftEdge hF).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow (d.productSquare hF)) rfl).trans
      (d.productSquare_left_native_arrow hF)

/-- 同じ右辺の類は、元の完備化後の二脚の実積射。 -/
lemma productRightEdge_class : Truncated.HomotopyCategory.homMk (d.productRightEdge
  hF).toTruncated =
    SpectrumHo.hom (d.productLegMap F) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (d.productRightEdge hF).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (d.productSquare hF)) rfl).trans
      (d.productSquare_right_arrow hF)

/-- 元の四つの指定した実 BF 射を持つ実境界。 -/
def productNewFrame : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueProductInclusion F))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.lift (𝟙 (perfectInvariantSpectrum F d.sequence.rightVertex)) (𝟙
    (perfectInvariantSpectrum F d.sequence.rightVertex))))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueKernelMap F))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.productLegMap F))

/-- 元の四辺を指定した実 BF 射へ移す、同じ端点固定の境界 homotopy。 -/
def productBoundaryHomotopy : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (d.productOldFrame hF) (d.productNewFrame (F
  := F)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy (X := Sp.{u})
    (d.productBottomEdge hF)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueProductInclusion F))
    (d.productTopEdge hF) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.lift (𝟙 (perfectInvariantSpectrum F
      d.sequence.rightVertex)) (𝟙 (perfectInvariantSpectrum F d.sequence.rightVertex))))
    (d.productLeftEdge hF)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueKernelMap F))
    (d.productRightEdge hF) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.productLegMap F))
    (d.productBottomEdge_class hF) (d.productTopEdge_class hF)
    (d.productLeftEdge_class hF) (d.productRightEdge_class hF)

/-- 同じ境界 homotopy の、元の全正方形への実延長。 -/
def productBoundaryExtension : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.pathFrame (d.productBoundaryHomotopy hF))
    (d.productSquare hF) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.extension (d.productBoundaryHomotopy hF)) _ (d.productOldFrame_eq hF)

/-- 指定した四つの実 BF 射を辺に持つ、同じ元の全正方形の移送先。 -/
def normalizedProductSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  (d.productBoundaryExtension hF).target

/-- 元の正方形と境界を移した全正方形との実関手同型。 -/
def normalizedProductComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.productSquare hF) (d.normalizedProductSquare hF) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.comparison (d.productBoundaryExtension hF))

/-- 移送後の境界は、元の四つの指定 BF 射の境界そのもの。 -/
lemma normalizedProductSquare_boundary : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ d.normalizedProductSquare hF =
    (d.productNewFrame (F := F)).diagram :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.extension_target_boundary (d.productBoundaryHomotopy hF)) _ (d.productOldFrame_eq hF)

/-- 同じ全正方形の関手同型は、実 Sp の引き戻し性を保つ。 -/
lemma normalizedProductSquare_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.normalizedProductSquare hF) :=
  (d.productSquare_isPullback hF).of_functorIso
    (d.normalizedProductComparison hF)

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
