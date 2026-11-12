module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderEndpoints

/-!
概要：パラメータだけを保持する二対象の円柱のための一点豊穣圏。
方針：全 Hom を単体集合の単位とし、単位と合成を一意な射で与える。
規約：対象の宇宙は任意。使われ方：円柱の nerve の積からの pairing。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder

/-- パラメータだけを持つ円柱の一点の底。 -/
structure Point where
  /-- 一意な対象。 -/
  val : PUnit.{v + 1}

/-- 全 Hom が単位である一点の豊穣構造。 -/
instance pointEnrichedCategory : EnrichedCategory SSet.{u} _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v} where
  Hom _ _ := 𝟙_ SSet.{u}
  id _ := 𝟙 _
  comp _ _ _ := fst _ _
  id_comp _ _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    rfl
  comp_id _ _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    rfl
  assoc _ _ _ _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
    rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pointEnrichedCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pointEnrichedCategory := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pointEnrichedCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.casesOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.mk := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.rec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.recOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.val (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.val := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.val

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pointEnrichedCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pointEnrichedCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pointEnrichedCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pointEnrichedCategory._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pointEnrichedCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pointEnrichedCategory._proof_3

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Point.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.mk.sizeOf_spec
