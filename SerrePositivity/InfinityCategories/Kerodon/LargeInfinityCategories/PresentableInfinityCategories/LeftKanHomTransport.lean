module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.UniversalProperty

/-!
概要：指定左 Kan Hom 比較の全単射性を同型で移す。
方針：元の前合成関手と同型による Hom 全単射で比較写像を共役する。
規約：指定単位を保持する。使われ方：分類模型と元の共変 Hom との比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：指定左 Kan Hom 比較の全単射性は標的の同型で移せる。
方針：標的同型の前後合成で比較写像を共役する。
規約：同じ単位を保持する。使われ方：分類された標的から任意の標的への移送。 -/
lemma leftKanHomMap_bijective_of_iso_target {A B X : SSet.{u}} (k : A ⟶ B)
    {F : A ⟶ X} {L G H : B ⟶ X} (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F (k ≫ L))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G H) (h : Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap k β G)) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap k β H) := by
  let r := (hoFunctor.map ((pre k).app X)).toFunctor
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap k β H =
      (Iso.homToEquiv (r.mapIso e)) ∘ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap k β G) ∘
        (Iso.homToEquiv e).symm := by
    funext η
    change β ≫ r.map η = (β ≫ r.map (η ≫ e.inv)) ≫ r.map e.hom
    calc
      β ≫ r.map η = β ≫ r.map η ≫ r.map (𝟙 _) := by simp
      _ = β ≫ r.map η ≫ r.map (e.inv ≫ e.hom) := by rw [Iso.inv_hom_id]
      _ = (β ≫ r.map (η ≫ e.inv)) ≫ r.map e.hom := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [he]
  exact (Iso.homToEquiv (r.mapIso e)).bijective.comp
    (h.comp (Iso.homToEquiv e).symm.bijective)

/-- 概要：指定左 Kan 単位の全 Hom 普遍性は始点と延長の同型で移せる。
方針：始点同型の前合成と延長同型の逆の前合成で比較写像を共役する。
規約：指定同型と元の単位を保持する。使われ方：分類模型から元の共変 Hom への移送。 -/
lemma leftKanHomUniversal_iso_unit {A B X : SSet.{u}} (k : A ⟶ B)
    {F F' : A ⟶ X} {L L' : B ⟶ X} (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F (k ≫ L))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal k β) (eF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F' F) (eL : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso L' L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal k (eF.hom ≫ β ≫ (eL.precomp k).inv) := by
  intro H
  have h := (Iso.homFromEquiv eF.symm
      (Z := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (k ≫ H)))).bijective.comp
    ((hβ H).comp (Iso.homFromEquiv eL
      (Z := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H))).bijective)
  convert h using 1
  funext η
  change (eF.hom ≫ β ≫
      (hoFunctor.map ((pre k).app X)).toFunctor.map eL.inv) ≫
        (hoFunctor.map ((pre k).app X)).toFunctor.map η =
    eF.hom ≫ (β ≫ (hoFunctor.map ((pre k).app X)).toFunctor.map (eL.inv ≫ η))
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：指定単位の同型による可換正方形は左 Kan Hom 普遍性を移す。
方針：始点同型を打ち消して指定単位を共役表示し、同型による移送を適用する。
規約：結論は指定された γ 自身。使われ方：coslice 単位から始点固定 Hom 単位への移送。 -/
lemma leftKanHomUniversal_of_unit_iso_square {A B X : SSet.{u}} (k : A ⟶ B)
    {F F' : A ⟶ X} {L L' : B ⟶ X}
    (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F (k ≫ L)) (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F' (k ≫ L'))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal k β) (eF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F F') (eL : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso L L')
    (h : eF.hom ≫ γ = β ≫ (eL.precomp k).hom) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal k γ := by
  have hγ : γ = eF.inv ≫ β ≫ (eL.precomp k).hom := by
    apply (cancel_epi eF.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact h
  have ht := leftKanHomUniversal_iso_unit k β hβ eF.symm eL.symm
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal k (eF.inv ≫ β ≫ (eL.precomp k).hom) at ht
  rwa [← hγ] at ht

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
