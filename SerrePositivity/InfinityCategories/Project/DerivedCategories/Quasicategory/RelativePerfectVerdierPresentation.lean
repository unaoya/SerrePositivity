module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagramComparison
public import SerrePositivity.KST.SConstruction.PerfectLocalizingInvariant
public import SerrePositivity.KST.SConstruction.PerfectVerdierPresentation

/-!
概要：固定した Cat^perf 提示上の実四角形を、strict 商と完備化の合成で認証する。
方針：K-S• 正本の PerfectVerdierSequence をそのまま使い、元の四角形を像に取る。
規約：完備化後の商辺に strict 局所化を要求しない。既存の厳密版は変更しない。
使われ方：固定 ν の実長方形と Cat^perf 局所化不変量への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram
end SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 元の源四角形と、実 strict 商・実完備化を保つ同じ Cat^perf 像。 -/
structure RelativePerfectVerdierDiagram {S : SSet.{u + 1}}
    (ν : S ⟶ perfectStableInfinity.{u}) where
  square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S
  image : PerfectVerdierDiagram.{u}
  image_eq : square ≫ ν = image.square

namespace RelativePerfectVerdierDiagram

variable {S : SSet.{u + 1}} (ν : S ⟶ perfectStableInfinity.{u})

/-- 元の二辺と零角を、完備化後の右射を持つ実 ν 像へ束ねる。 -/
def ofSquare (d : PerfectVerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F ≫ ν = SSet.yonedaEquiv.symm
      (perfectStableArrow d.verdier.inclusion d.left_complete d.middle_complete).edge)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F ≫ ν = SSet.yonedaEquiv.symm
      (perfectStableArrow d.projection d.middle_complete d.right_complete).edge)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ ν) 0 1))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν where
  square := F
  image := {
    toPerfectVerdierSequence := d
    square := F ≫ ν
    left_eq := by
      have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (F ≫ ν)
      rw [hb, Equiv.apply_symm_apply,
        (perfectStableArrow d.verdier.inclusion d.left_complete d.middle_complete).src_eq] at h
      exact h.symm
    middle_eq := by
      have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target (F ≫ ν)
      rw [hb, Equiv.apply_symm_apply,
        (perfectStableArrow d.verdier.inclusion d.left_complete d.middle_complete).tgt_eq] at h
      exact h.symm
    right_eq := by
      have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (F ≫ ν)
      rw [hr, Equiv.apply_symm_apply,
        (perfectStableArrow d.projection d.middle_complete d.right_complete).tgt_eq] at h
      exact h.symm
    bottom_edge := by
      rw [← Category.assoc, hb]
      exact perfectStableArrow_inclusion _ _ _
    right_edge := by
      rw [← Category.assoc, hr]
      exact perfectStableArrow_inclusion _ _ _
    zero_corner := hz }
  image_eq := rfl

@[simp] lemma ofSquare_square (d : PerfectVerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S) (hb hr hz) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare ν d F hb hr hz).square = F := rfl

/-- 固定 ν の StableInfinity 像で照合された元の二辺も、同じ完備化付き証明書になる。 -/
def ofStableSquare (d : PerfectVerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F ≫ ν ≫ perfectStableInfinityInclusion =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.verdier.inclusion).edge)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F ≫ ν ≫ perfectStableInfinityInclusion =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ ν) 0 1))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare ν d F
  · apply (cancel_mono perfectStableInfinityInclusion).mp
    exact (Category.assoc _ _ _).trans
      (hb.trans (perfectStableArrow_inclusion _ _ _).symm)
  · apply (cancel_mono perfectStableInfinityInclusion).mp
    exact (Category.assoc _ _ _).trans
      (hr.trans (perfectStableArrow_inclusion _ _ _).symm)
  · exact hz

/-- 元の源四角形の同じ零角は、固定した完備提示でも零安定圏を表す。 -/
lemma zero_corner (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject
      (ν.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 1))) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.square ≫ ν) 0 1))
  rw [d.image_eq]
  exact d.image.zero_corner

/-- Cat^perf 不変量の元の制限値と同じ零角を持つ相対三角形。 -/
def fiberTriangle {E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}}
    (hE : IsPerfectLocalizingInvariant E) (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle _root_.SerrePositivity.KST.Spectra.Sp.{u} where
  square := d.square ≫ ν ≫ E
  zero_corner := hE.preservesZero _ (d.zero_corner ν)

/-- 相対値は同じ Cat^perf 不変量の制限であり、新たな局所化条件は入力しない。 -/
lemma isPullback {E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}}
    (hE : IsPerfectLocalizingInvariant E) (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ ν ≫ E) := by
  rw [← Category.assoc, d.image_eq]
  exact hE.preservesVerdier d.image

lemma fiberTriangle_isFiber {E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}}
    (hE : IsPerfectLocalizingInvariant E) (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence (d.fiberTriangle ν hE) := d.isPullback ν hE

/-- 元の三指定境界を保つ全源四角形同型で、同じ不変量値の pullback を運ぶ。 -/
lemma isPullback_of_sourceIso {E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}}
    (hE : IsPerfectLocalizingInvariant E) (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν)
    {F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso d.square F) (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso d.square F b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ ν ≫ E) :=
  (d.isPullback ν hE).of_functorIso (e.comparison.postcomp (ν ≫ E))

end RelativePerfectVerdierDiagram
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.casesOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.fiberTriangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.fiberTriangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.fiberTriangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.fiberTriangle_isFiber := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.fiberTriangle_isFiber

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.image (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.image := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.image

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.image_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.image_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.isPullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.isPullback

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.isPullback_of_sourceIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.isPullback_of_sourceIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.mk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare_square := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare_square

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofStableSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStableSquare := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofStableSquare

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.rec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.recOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.square (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.square := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.zero_corner := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.zero_corner

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.fiberTriangle._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.fiberTriangle._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofSquare._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStableSquare._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofStableSquare._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStableSquare._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofStableSquare._proof_2
