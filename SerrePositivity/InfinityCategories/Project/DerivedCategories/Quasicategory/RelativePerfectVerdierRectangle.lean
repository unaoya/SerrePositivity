module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagramComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierPresentation

/-!
概要：固定 Cat^perf 提示の完備化付き二面から、元の比較正方形の pullback を得る。
方針：二面を同じ源長方形から取り、不変量値で実 pullback の貼合せを消去する。
規約：指定境界を持つ全図式同型で輸送し、strict 商と完備化を混同しない。
使われ方：K-S• の実長方形と K-B の固定 ν 相対屋根。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 実長方形の二つの面は、元の strict 商と完備化を保持する。 -/
structure RelativePerfectVerdierRectangle {S : SSet.{u + 1}}
    (ν : S ⟶ perfectStableInfinity.{u}) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S
  right : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν
  outer : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν
  right_eq : right.square = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ diagram
  outer_eq : outer.square = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ diagram

namespace RelativePerfectVerdierRectangle

variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}

/-- 同じ ν 像の ofSquare 認証を、元の源長方形へ貼る。 -/
def ofActualFaces (F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν)
    (hr : r.square = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ F)
    (ho : o.square = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle ν := ⟨F, r, o, hr, ho⟩

/-- Cat^perf 不変量の同じ制限で、元の第三面が pullback になる。 -/
lemma comparisonSquare_isPullback (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle ν)
    {E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 2) ≫ ν ≫ E) := by
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (d.diagram ≫ ν ≫ E) 0) := by
    have h := d.right.isPullback ν hE
    rw [d.right_eq] at h
    exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose _).mpr h
  have hO : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (d.diagram ≫ ν ≫ E) 1) := by
    have h := d.outer.isPullback ν hE
    rw [d.outer_eq] at h
    exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose _).mpr h
  exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose _).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isPullbackSquare_pasting_cancel_right (d.diagram ≫ ν ≫ E) hR hO)

/-- 指定包含辺・商辺・零角を保つ全源同型に沿って、同じ値の pullback を運ぶ。 -/
lemma comparison_isPullback_of_sourceIso (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle ν)
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso d.diagram F)
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso d.diagram F b)
    {E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ ν ≫ E) := by
  let c := (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1}))
  exact (d.comparisonSquare_isPullback hE).of_functorIso
    ((e.comparison.precomp c).postcomp (ν ≫ E))

end RelativePerfectVerdierRectangle
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
