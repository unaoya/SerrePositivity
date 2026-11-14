module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle

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

/-- 絶対の完備化付き提示から、元の実 ν 四角形へ指定全境界比較を運ぶ。
提示の源 S への厳密な持ち上げや、商辺の厳密等式を追加入力にしない。 -/
lemma RelativePerfectVerdierDiagram.isPullback_of_perfectImageIso
    (d : PerfectVerdierDiagram.{u}) (hE : IsPerfectLocalizingInvariant E)
    {F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso d.square (F ≫ ν))
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso d.square (F ≫ ν) b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ ν ≫ E) :=
  (hE.preservesVerdier d).of_functorIso (e.comparison.postcomp E)

/-- 実 S 長方形の二面を、それぞれの絶対提示との指定全比較で認証する。
二面の S 内の別代表は選ばず、同じ長方形の第三面で貼合せを消去する。 -/
lemma RelativePerfectVerdierRectangle.comparison_isPullback_of_actualFaces
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : PerfectVerdierDiagram.{u}) (hE : IsPerfectLocalizingInvariant E)
    (br : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso r.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ F ≫ ν))
    (er : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso r.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ F ≫ ν) br)
    (bo : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso o.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ F ≫ ν))
    (eo : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso o.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ F ≫ ν) bo) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ ν ≫ E) := by
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (F ≫ ν ≫ E) 0) :=
    (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose _).mpr
      (RelativePerfectVerdierDiagram.isPullback_of_perfectImageIso r hE br er)
  have hO : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (F ≫ ν ≫ E) 1) :=
    (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose _).mpr
      (RelativePerfectVerdierDiagram.isPullback_of_perfectImageIso o hE bo eo)
  exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose _).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isPullbackSquare_pasting_cancel_right (F ≫ ν ≫ E) hR hO)

/-- 実二面による認証と、上下二単体を含む指定全長方形比較を接続する。 -/
lemma RelativePerfectVerdierRectangle.comparison_isPullback_of_actualFaces_imageIso
    (G : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : PerfectVerdierDiagram.{u}) (hE : IsPerfectLocalizingInvariant E)
    (br : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso r.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ G ≫ ν))
    (er : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso r.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ G ≫ ν) br)
    (bo : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso o.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ G ≫ ν))
    (eo : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso o.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ G ≫ ν) bo)
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u}}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (G ≫ ν) F)
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (G ≫ ν) F b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ E) := by
  let c := (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1}))
  exact (comparison_isPullback_of_actualFaces G r o hE br er bo eo).of_functorIso
    ((e.comparison.precomp c).postcomp E)

/-- 元の源四角形は固定し、その実 ν 像の全境界付き比較を値へ運ぶ。 -/
lemma RelativePerfectVerdierDiagram.isPullback_of_imageIso
    (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν) (hE : IsPerfectLocalizingInvariant E)
    {F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (d.square ≫ ν) (F ≫ ν))
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (d.square ≫ ν) (F ≫ ν) b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ ν ≫ E) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((d.square ≫ ν) ≫ E) := d.isPullback ν hE
  exact h.of_functorIso (e.comparison.postcomp E)

/-- 実 ν 長方形の全比較を使い、二面・上下の合成三角形を保って第三面を輸送する。 -/
lemma RelativePerfectVerdierRectangle.comparison_isPullback_of_imageIso
    (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle ν) (hE : IsPerfectLocalizingInvariant E)
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (d.diagram ≫ ν) (F ≫ ν))
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (d.diagram ≫ ν) (F ≫ ν) b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ ν ≫ E) := by
  let c := (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1}))
  exact (d.comparisonSquare_isPullback hE).of_functorIso
    ((e.comparison.precomp c).postcomp E)

end SerrePositivity.KST.LocalizingInvariants
