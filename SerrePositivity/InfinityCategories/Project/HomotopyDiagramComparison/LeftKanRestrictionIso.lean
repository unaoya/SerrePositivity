module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalRestrictionHom

/-!
概要：恒等単位を持つ二つの元の左 Kan 延長は、制限の全自然同型から全自然同型を得る。
方針：元の制限の Hom 全単射で同型と逆を持ち上げ、同じ制限の単射性で逆関係を示す。
規約：比較は元の前合成関手自身に沿い、対象ごとの同型へ置き換えない。
使われ方：全前層密度から得た Yoneda Hom・宇宙変更の大域比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の恒等単位付き左 Kan 延長から出る射の、元の制限は全単射。 -/
lemma leftKanReflRestriction_bijective {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ (δ ≫ F) F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F))) (G : C ⟶ D) :
    Function.Bijective
      ((hoFunctor.map ((pre δ).app D)).toFunctor.map : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G → _) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal δ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F)) hF G
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom] at h
  change Function.Bijective (fun α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G ↦
    𝟙 _ ≫ (hoFunctor.map ((pre δ).app D)).toFunctor.map α) at h
  simpa only [Category.id_comp] using h

/-- 元の二つの左 Kan 延長の制限の同型は、同じ全関手の同型へ持ち上がる。 -/
def leftKanReflRestrictionIso {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) {F G : C ⟶ D}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ (δ ≫ F) F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F)))
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ (δ ≫ G) G (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ G)))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (δ ≫ F) (δ ≫ G)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := by
  let R := (hoFunctor.map ((pre δ).app D)).toFunctor
  let a := Classical.choose ((leftKanReflRestriction_bijective δ F hF G).surjective e.hom)
  let b := Classical.choose ((leftKanReflRestriction_bijective δ G hG F).surjective e.inv)
  have ha := Classical.choose_spec
    ((leftKanReflRestriction_bijective δ F hF G).surjective e.hom)
  have hb := Classical.choose_spec
    ((leftKanReflRestriction_bijective δ G hG F).surjective e.inv)
  refine ⟨a, b, ?_, ?_⟩
  · apply (leftKanReflRestriction_bijective δ F hF F).injective
    change R.map (a ≫ b) = R.map (𝟙 _)
    rw [R.map_comp, ha, hb, e.hom_inv_id, R.map_id]
    rfl
  · apply (leftKanReflRestriction_bijective δ G hG G).injective
    change R.map (b ≫ a) = R.map (𝟙 _)
    rw [R.map_comp, hb, ha, e.inv_hom_id, R.map_id]
    rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
