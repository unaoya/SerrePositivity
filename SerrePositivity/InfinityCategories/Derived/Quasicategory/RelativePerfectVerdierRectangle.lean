module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierDiagramComparison
public import SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierPresentation

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
namespace SerrePositivity.InfinityCategories.Derived.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

/-- 実長方形の二つの面は、元の strict 商と完備化を保持する。 -/
structure RelativePerfectVerdierRectangle {S : SSet.{u + 1}}
    (ν : S ⟶ perfectStableInfinity.{u}) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S
  right : _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram ν
  outer : _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram ν
  right_eq : right.square = _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierRectangleFace 0 ≫ diagram
  outer_eq : outer.square = _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierRectangleFace 1 ≫ diagram

namespace RelativePerfectVerdierRectangle
open _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle
variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}

/-- 同じ ν 像の ofSquare 認証を、元の源長方形へ貼る。 -/
def ofActualFaces (F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram ν)
    (hr : r.square = _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierRectangleFace 0 ≫ F)
    (ho : o.square = _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierRectangleFace 1 ≫ F) :
    _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle ν := ⟨F, r, o, hr, ho⟩

/-- Cat^perf 不変量の同じ制限で、元の第三面が pullback になる。 -/
lemma comparisonSquare_isPullback (d : _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle ν)
    {E : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}}
    (hE : IsPerfectLocalizingInvariant E) :
    IsPullbackSquare (((β_ _ _).hom ≫ pastingSquare d.diagram 2) ≫ ν ≫ E) := by
  have hR : IsPullbackSquare (pastingSquare (d.diagram ≫ ν ≫ E) 0) := by
    have h := d.right.isPullback ν hE
    rw [d.right_eq] at h
    exact (isPullbackSquare_iff_transpose _).mpr h
  have hO : IsPullbackSquare (pastingSquare (d.diagram ≫ ν ≫ E) 1) := by
    have h := d.outer.isPullback ν hE
    rw [d.outer_eq] at h
    exact (isPullbackSquare_iff_transpose _).mpr h
  exact (isPullbackSquare_iff_transpose _).mp
    (isPullbackSquare_pasting_cancel_right (d.diagram ≫ ν ≫ E) hR hO)

/-- 指定包含辺・商辺・零角を保つ全源同型に沿って、同じ値の pullback を運ぶ。 -/
lemma comparison_isPullback_of_sourceIso (d : _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle ν)
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso d.diagram F)
    (e : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso d.diagram F b)
    {E : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}}
    (hE : IsPerfectLocalizingInvariant E) :
    IsPullbackSquare (((β_ _ _).hom ≫ pastingSquare F 2) ≫ ν ≫ E) := by
  let c := (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1}))
  exact (d.comparisonSquare_isPullback hE).of_functorIso
    ((e.comparison.precomp c).postcomp (ν ≫ E))

end RelativePerfectVerdierRectangle
end SerrePositivity.InfinityCategories.Derived.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.casesOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.comparisonSquare_isPullback := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.comparisonSquare_isPullback

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.comparison_isPullback_of_sourceIso := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.comparison_isPullback_of_sourceIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.diagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.diagram := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.diagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.mk := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ofActualFaces (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.ofActualFaces := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ofActualFaces

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.outer (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.outer := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.outer

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.outer_eq := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.outer_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.rec := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.right := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.right_eq := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.right_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.ofActualFaces._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ofActualFaces._proof_1
