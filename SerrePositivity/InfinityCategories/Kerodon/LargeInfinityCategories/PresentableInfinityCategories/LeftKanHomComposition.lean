module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomUniversal

/-!
概要：指定された二つの左 Kan 単位の大域的 Hom 普遍性を合成する。
方針：元の前合成関手の合成式で、同じ合成単位の比較写像を二つの全単射に分解する。
規約：点ごとの Kan 条件の合成はまだ結論しない。両単位の元の類を保持する。
使われ方：既に存在する二つの余極限頂点を、Kan の一意性で比較する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {A B C D : SSet.{u}}
  (p : A ⟶ B) (q : B ⟶ C) {F : A ⟶ D} {G : B ⟶ D} {H : C ⟶ D}

/-- 元の二つの単位を、元の前合成関手を使って合成した単位。 -/
def leftKanCompositeUnit (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F (p ≫ G)) (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G (q ≫ H)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F ((p ≫ q) ≫ H) :=
  β ≫ (hoFunctor.map ((pre p).app D)).toFunctor.map γ

/-- 同じ合成単位の Hom 比較は、元の二つの Hom 比較の合成。 -/
lemma leftKanCompositeUnit_homMap (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F (p ≫ G))
    (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G (q ≫ H)) (T : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap (p ≫ q) (leftKanCompositeUnit p q β γ) T =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap p β (q ≫ T)) ∘ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap q γ T) := by
  funext η
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap, leftKanCompositeUnit, Function.comp_apply]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  congr 1
  congr 1
  have hpq : (hoFunctor.map ((pre q).app D)).toFunctor ⋙
      (hoFunctor.map ((pre p).app D)).toFunctor =
      (hoFunctor.map ((pre (p ≫ q)).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  simpa only [CategoryTheory.Functor.comp_map, eqToHom_refl, Category.id_comp,
    Category.comp_id] using (CategoryTheory.Functor.congr_hom hpq η).symm

/-- 大域的 Hom 普遍性は、元の指定単位の合成について保たれる。 -/
lemma leftKanHomUniversal_comp (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F (p ≫ G)) (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G (q ≫ H))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal p β) (hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal q γ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal (p ≫ q) (leftKanCompositeUnit p q β γ) := by
  intro T
  rw [leftKanCompositeUnit_homMap]
  exact (hβ (q ≫ T)).comp (hγ T)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
