module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitConstantFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomUniversal

/-!
概要：標準局所余極限条件から元の制限の全パラメータ Hom 全単射を得る。
方針：恒等指定変換の輸送を使い、既存の Kan の Hom 普遍性を定値族へ適用する。
規約：比較写像は δ による前合成そのもの。
使われ方：元の Kan 関手から出る実際の写像空間の制限の判定。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標準局所余錐の余極限性は恒等指定変換に対する左 Kan 条件を与える。
方針：恒等変換の定値な局所輸送を選ぶ。
規約：元の図式は δ による F の制限。
使われ方：標準局所条件を指定変換つきの既存の Hom 普遍性へ接続する。 -/
lemma kanLeftKanExtension_refl_of_canonicalColimits {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ (δ ≫ F) F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F)) := by
  intro c
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftReflTransport δ F c, ?_⟩
  exact hF c

/-- 概要：標準左 Kan 関手から出る h Fun の射の制限は全単射。
方針：恒等指定変換の Hom 普遍性で、前置された恒等射を消去する。
規約：標的 G に Kan 条件を要求しない。
使われ方：元の関手の全部分圏の制限の写像空間の比較。 -/
lemma kanLeftCanonicalHomMap_bijective {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)) (G : C ⟶ D) :
    Function.Bijective
      ((hoFunctor.map ((pre δ).app D)).toFunctor.map : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G → _) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal δ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F))
    (kanLeftKanExtension_refl_of_canonicalColimits δ F hF) G
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom] at h
  change Function.Bijective (fun α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G ↦
    𝟙 _ ≫ (hoFunctor.map ((pre δ).app D)).toFunctor.map α) at h
  simpa only [Category.id_comp] using h

/-- 概要：標準左 Kan 関手の定値パラメータ族から出る射の制限は全単射。
方針：局所余極限を定値族へ移し、関手圏に値を取る Hom 制限の判定を適用する。
規約：パラメータ A と標的の図式 G は任意。
使われ方：元の Kan 制限の写像空間を全パラメータの Hom で比較する入力。 -/
lemma kanLeftCanonicalHomMap_constantFamily_bijective {A K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c))
    (G : C ⟶ (ihom A).obj D) :
    Function.Bijective
      ((hoFunctor.map ((pre δ).app ((ihom A).obj D))).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) G → _) :=
  kanLeftCanonicalHomMap_bijective δ (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.leftCanonicalColimits_constantFamily δ F hF) G

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
