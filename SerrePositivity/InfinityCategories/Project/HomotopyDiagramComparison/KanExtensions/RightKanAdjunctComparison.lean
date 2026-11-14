module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.UnitComparisons.ArbitraryParameterAdjunct
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.UniversalProperty

/-!
概要：元の標準単位の Hom 対応と指定右 Kan 変換の大域的 Hom 比較を照合する。
方針：同じ標準単位の式と、直積パラメータ上の Hom 全単射を照合する。
規約：添字の quasicategory 性を仮定しない。使われ方：一般 coherent 極限の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 指定右 Kan 変換の Hom 比較と、元の標準単位の対応は可換である。 -/
lemma rightKanHomMap_parameterUnitHomMap {K C X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (δ : K ⟶ C)
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    {d : K ⟶ Y} {H : C ⟶ Y} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ H) d)
    (T : C ⟶ X) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (T ≫ F) H) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap η (δ ≫ T) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap δ α (T ≫ F) β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap (F := H ≫ G) (F₀ := d ≫ G) δ
        ((hoFunctor.map ((ihom K).map G)).toFunctor.map α) T
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap η T H β) := by
  have hr := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap_naturality_right (F := F) (G := G) η (δ ≫ T)
    (V := δ ≫ H) (V' := d) ((hoFunctor.map ((pre δ).app Y)).toFunctor.map β) α
  have hp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap_precomp η δ T H β
  exact hr.trans (congrArg (fun e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ T) ((δ ≫ H) ≫ G) ↦
    e ≫ (hoFunctor.map ((ihom K).map G)).toFunctor.map α) hp)

/-- 元の右 Kan 変換の大域的 Hom 普遍性は、右随伴による後合成で保たれる。 -/
lemma rightKanHomUniversal_postcomp_of_unitCondition {K C X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (δ : K ⟶ C)
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) {d : K ⟶ Y} {H : C ⟶ Y}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ H) d) (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal δ α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal (F := H ≫ G) (F₀ := d ≫ G) δ
      ((hoFunctor.map ((ihom K).map G)).toFunctor.map α) := by
  intro T
  have hs := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap_bijective η hη T H
  have ht := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap_bijective η hη (δ ≫ T) d
  have hb := hα (T ≫ F)
  constructor
  · intro β γ he
    obtain ⟨β', rfl⟩ := hs.surjective β
    obtain ⟨γ', rfl⟩ := hs.surjective γ
    rw [← rightKanHomMap_parameterUnitHomMap, ← rightKanHomMap_parameterUnitHomMap] at he
    have h := hb.injective (ht.injective he)
    subst γ'
    rfl
  · intro β
    obtain ⟨β', rfl⟩ := ht.surjective β
    obtain ⟨γ', hγ'⟩ := hb.surjective β'
    refine ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap η T H γ', ?_⟩
    rw [← rightKanHomMap_parameterUnitHomMap, hγ']

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
