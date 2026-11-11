module

public import SerrePositivity.KST.LocalizingInvariants.RelativeVerdierDiagramComparison
public import SerrePositivity.KST.SConstruction.DGOdotVerdierRectangle
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：実 ν 像で認証した長方形と、K-S• の既存の厳密入力を接続する。
方針：指定境界を持つ全比較と、厳密代表への S 内の比較を別の入力にする。
規約：既存の image_eq・宣言名・型は変えず、厳密代表の存在を結論しない。
使われ方：同じ相対不変量の pullback を、供給された厳密代表へ輸送する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants

variable {R : Type u} [CommRing R] {d : DGOdotInput R}

/-- 元の源長方形の実認証と、指定した包含・商・零角・合成三角形の全比較。
各欄の存在は未供給であり、この入力型の定義を完成には数えない。 -/
structure DGOdotVerdierRectangleComparisonInput (h : DGOdotLaxVerdierInput R d) where
  rectangle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle (dgKInputNu.{u, u + 1} R)
  boundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (rectangle.diagram ≫ dgKInputNu R)
    (LaxUniversalDifference.rectangle (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)
      h.inclusion h.projection h.isVerdier).diagram
  image : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (rectangle.diagram ≫ dgKInputNu R)
    (LaxUniversalDifference.rectangle (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)
      h.inclusion h.projection h.isVerdier).diagram boundary
  source_vertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex rectangle.comparisonSquare 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)

/-- 厳密版へ輸送するための追加の実代表。ν 像の同型だけからは構成しない。 -/
structure DGOdotVerdierRectangleStrictTransport {h : DGOdotLaxVerdierInput R d}
    (v : DGOdotVerdierRectangleComparisonInput h) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R
  image_eq : diagram ≫ dgKInputNu R =
    (LaxUniversalDifference.rectangle (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)
      h.inclusion h.projection h.isVerdier).diagram
  boundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso v.rectangle.diagram diagram
  source : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso v.rectangle.diagram diagram boundary
  image_comparison : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (source.comparison.postcomp (dgKInputNu R))
    rfl image_eq = v.image.comparison
  source_vertex_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 2) 0 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex v.rectangle.comparisonSquare 0 0

namespace DGOdotVerdierRectangleComparisonInput
variable {h : DGOdotLaxVerdierInput R d} (v : DGOdotVerdierRectangleComparisonInput h)

/-- 比較後の絶対図式を使わず、同じ源長方形の相対認証で値の pullback を得る。 -/
theorem comparison_isPullback {E : dgKInputInfinity.{u, u + 1} R ⟶ Spectra.Sp.{u + 1}}
    (hE : IsDGKRelativeLocalizingInvariant R E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (v.rectangle.comparisonSquare ≫ E) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonSquare_isPullback v.rectangle) hE

/-- 指定した実厳密代表を、従来どおりの型・名前の入力へ輸送する。 -/
def toStrict (t : DGOdotVerdierRectangleStrictTransport v) :
    DGOdotVerdierRectangleInput h where
  diagram := t.diagram
  image_eq := t.image_eq
  source_vertex := t.source_vertex_eq.trans v.source_vertex

@[simp] lemma toStrict_diagram (t : DGOdotVerdierRectangleStrictTransport v) :
    (v.toStrict t).diagram = t.diagram := rfl

/-- 同じ E の値を S 内の全図式比較で従来の厳密比較四角形へ輸送する。 -/
theorem toStrict_comparison_isPullback (t : DGOdotVerdierRectangleStrictTransport v)
    {E : dgKInputInfinity.{u, u + 1} R ⟶ Spectra.Sp.{u + 1}}
    (hE : IsDGKRelativeLocalizingInvariant R E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((v.toStrict t).comparisonSquare ≫ E) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparison_isPullback_of_sourceIso v.rectangle) t.boundary t.source hE

/-- 輸送後も左端は元の dg 対角始域そのもの。 -/
theorem toStrict_source (t : DGOdotVerdierRectangleStrictTransport v) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (v.toStrict t).comparisonSquare 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d) :=
  (v.toStrict t).comparison_source

end DGOdotVerdierRectangleComparisonInput
end SerrePositivity.KST.LocalizingInvariants
