module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionFamily

/-!
概要：under 圏上の元の切断の族は、元の底上の left fibration の通常の strict 図式をなす。
方針：既存の under 制限の厳密な関手則と、パラメータを保つ制限の合成則を組み合わせる。
規約：辺のホモトピー類で商にせず、恒等と合成を射の等式として証明する。
使われ方：coherent 前層図式を strict right fibration 図式へ移す構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 同じ under 切断の制限は恒等を厳密に保つ。 -/
lemma underSectionFamilyMap_id (i : I) : underSectionFamilyMap p (𝟙 i) = 𝟙 _ := by
  apply parametrizedSections_hom_ext p _
  · rw [underSectionFamilyMap, parametrizedSectionsPre_map, nerveUnderMap_id,
      pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]
  · rw [underSectionFamilyMap, parametrizedSectionsPre_projection, Category.id_comp]

/-- 同じ under 切断の制限は合成を厳密に保つ。 -/
lemma underSectionFamilyMap_comp {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    underSectionFamilyMap p (f ≫ g) = underSectionFamilyMap p f ≫ underSectionFamilyMap p g := by
  apply parametrizedSections_hom_ext p _
  · simp only [underSectionFamilyMap]
    rw [parametrizedSectionsPre_map, Category.assoc, parametrizedSectionsPre_map,
      ← Category.assoc, parametrizedSectionsPre_map]
    rw [nerveUnderMap_comp, pre_map, NatTrans.comp_app, Category.assoc]
  · simp only [underSectionFamilyMap, Category.assoc, parametrizedSectionsPre_projection]

/-- 元の底を固定した left fibration の同じ strict 図式。 -/
def underSectionStrictDiagram [LeftFibration p] : I ⥤ LeftFibrationObject B where
  obj i := ⟨Over.mk (underSectionFamilyProjection p i),
    underSectionFamilyProjection_leftFibration p i⟩
  map f := Over.homMk (underSectionFamilyMap p f) (underSectionFamilyMap_projection p f)
  map_id i := by
    apply Over.OverMorphism.ext
    exact underSectionFamilyMap_id p i
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact underSectionFamilyMap_comp p f g

end SerrePositivity.InfinityCategories.F2.Ind
