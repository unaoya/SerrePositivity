module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderEndpoints

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
