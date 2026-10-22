module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderHomotopy
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinder

/-! # 同じ実写像円柱と二脚押し出しの基点固定比較
概要：元の実写像円柱源比較と、元の射を標的へ入れた合成は同じ写像空間の成分。
方針：同じ元の円柱射を区間族へ送り、実押し出しの両端の式を回収する。
規約：局所化等号からホモトピーを逆算しない。使われ方：構造射の随伴の Ω 条件。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open Spectra.PointedMapping

/-- 同じ実写像円柱の源比較は、元の射と標的包含の合成と同じ点つき成分。 -/
lemma pointedTensorMappingCylinderSource_component {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) :
    componentOf (f ≫ pointedTensorMappingCylinderTarget f) =
      componentOf (pointedTensorMappingCylinderSource f) := by
  have h := pointedTensorCylinderEnd_component (pointedTensorMappingCylinderCylinder f)
  rw [pointedTensorMappingCylinder_condition f] at h
  exact h

/-- 同じ二脚円柱押し出しの元の比較四角形は、基点固定の成分で可換。 -/
lemma pointedDoubleMappingCylinder_component_square
    {X A B : PointedSimplicialSet.{u}} (f : X ⟶ A) (g : X ⟶ B) :
    componentOf (f ≫ pointedTensorMappingCylinderTarget f ≫
      pushout.inl (pointedTensorMappingCylinderSource f) g) =
      componentOf (g ≫ pushout.inr (pointedTensorMappingCylinderSource f) g) := by
  have h := componentOf_comp_right (pointedTensorMappingCylinderSource_component f)
    (pushout.inl (pointedTensorMappingCylinderSource f) g)
  rw [pushout.condition] at h
  exact (congrArg componentOf (Category.assoc _ _ _)).symm.trans h

/-- 同じ二脚円柱押し出しの成分四角形は、任意の実射で後合成しても可換。 -/
lemma pointedDoubleMappingCylinder_component_square_post
    {X A B T : PointedSimplicialSet.{u}} (f : X ⟶ A) (g : X ⟶ B)
    (p : pushout (pointedTensorMappingCylinderSource f) g ⟶ T) :
    componentOf (f ≫ pointedTensorMappingCylinderTarget f ≫
      pushout.inl (pointedTensorMappingCylinderSource f) g ≫ p) =
      componentOf (g ≫ pushout.inr (pointedTensorMappingCylinderSource f) g ≫ p) := by
  have h := componentOf_comp_right (pointedDoubleMappingCylinder_component_square f g) p
  simpa only [Category.assoc] using h

end SerrePositivity.KST.SConstruction
