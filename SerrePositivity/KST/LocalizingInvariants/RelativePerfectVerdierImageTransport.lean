module

public import SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle

/-!
概要：完備化付き固定 ν 像の全図式比較から、不変量値の pullback を輸送する。
方針：包含辺・完備化後の商辺・零角の指定比較を保つ同型へ同じ Cat^perf 不変量を適用する。
規約：ν 像の同型から源 S の厳密代表を推論しない。
使われ方：K-S• の実長方形と固定 ν 上の相対懸垂屋根の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants
variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}
  {E : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}}

/-- 元の源四角形は固定し、その実 ν 像の全境界付き比較を値へ運ぶ。 -/
lemma RelativePerfectVerdierDiagram.isPullback_of_imageIso
    (d : RelativePerfectVerdierDiagram ν) (hE : IsPerfectLocalizingInvariant E)
    {F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : VerdierSquareBoundaryIso (d.square ≫ ν) (F ≫ ν))
    (e : VerdierSquareDiagramIso (d.square ≫ ν) (F ≫ ν) b) :
    IsPullbackSquare (F ≫ ν ≫ E) := by
  have h : IsPullbackSquare ((d.square ≫ ν) ≫ E) := d.isPullback ν hE
  exact h.of_functorIso (e.comparison.postcomp E)

/-- 実 ν 長方形の全比較を使い、二面・上下の合成三角形を保って第三面を輸送する。 -/
lemma RelativePerfectVerdierRectangle.comparison_isPullback_of_imageIso
    (d : RelativePerfectVerdierRectangle ν) (hE : IsPerfectLocalizingInvariant E)
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : VerdierRectangleBoundaryIso (d.diagram ≫ ν) (F ≫ ν))
    (e : VerdierRectangleDiagramIso (d.diagram ≫ ν) (F ≫ ν) b) :
    IsPullbackSquare (((β_ _ _).hom ≫ pastingSquare F 2) ≫ ν ≫ E) := by
  let c := (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1}))
  exact (d.comparisonSquare_isPullback hE).of_functorIso
    ((e.comparison.precomp c).postcomp E)

end SerrePositivity.KST.LocalizingInvariants
