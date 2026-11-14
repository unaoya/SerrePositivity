module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：κ-accessible 関手を、元の小さい κ-filtered 全余錐の保存として定義する。
方針：Ind の native な保存性を再利用し、恒等・合成・濃度変更を証明する。
規約：圏の accessibility は別の性質。関手の保存性に追加の instance を要求しない。
使われ方：HTT 5.4.2 の accessible 関手と後続の随伴関手定理。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
open _root_.SerrePositivity.InfinityCategories

/-- 宇宙 u の κ-filtered 余極限を保存する、元の宇宙 u+1 の関手。 -/
@[kerodon 06KY]
abbrev IsKappaAccessibleFunctor (κ : Cardinal.{u}) {C D : SSet.{u + 1}}
    (F : C ⟶ D) : Prop := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits κ F

/-- ある正則濃度の小さい filtered 余極限を保存する関手。 -/
@[kerodon 06KY]
def IsAccessibleFunctor {C D : SSet.{u + 1}} (F : C ⟶ D) : Prop :=
  ∃ κ : Cardinal.{u}, κ.IsRegular ∧ IsKappaAccessibleFunctor κ F

lemma isKappaAccessibleFunctor_id (κ : Cardinal.{u}) (C : SSet.{u + 1}) :
    IsKappaAccessibleFunctor κ (𝟙 C) := by
  intro I hI hκ D c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (Category.comp_id c.val)).mpr hc

lemma IsKappaAccessibleFunctor.comp {κ : Cardinal.{u}} {C D E : SSet.{u + 1}}
    {F : C ⟶ D} {G : D ⟶ E} (hF : IsKappaAccessibleFunctor κ F)
    (hG : IsKappaAccessibleFunctor κ G) : IsKappaAccessibleFunctor κ (F ≫ G) := by
  intro I hI hκ a c hc
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (F ≫ G) c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)) (Category.assoc c.val F G).symm).mpr
  exact hG I (a ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c) (hF I a c hc)

lemma IsKappaAccessibleFunctor.of_le {κ μ : Cardinal.{u}} (hκμ : κ ≤ μ)
    {C D : SSet.{u + 1}} {F : C ⟶ D} (h : IsKappaAccessibleFunctor κ F) :
    IsKappaAccessibleFunctor μ F := by
  intro I hI hμ a c hc
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_le hκμ
  exact h I a c hc

lemma IsKappaAccessibleFunctor.of_functorIso {κ : Cardinal.{u}}
    {C D : SSet.{u + 1}} [Quasicategory D] {F G : C ⟶ D}
    (h : IsKappaAccessibleFunctor κ F) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    IsKappaAccessibleFunctor κ G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits.of_functorIso h e

lemma IsAccessibleFunctor.comp {C D E : SSet.{u + 1}} {F : C ⟶ D} {G : D ⟶ E}
    (hF : IsAccessibleFunctor F) (hG : IsAccessibleFunctor G) :
    IsAccessibleFunctor (F ≫ G) := by
  obtain ⟨κ, hκ, hF⟩ := hF
  obtain ⟨μ, hμ, hG⟩ := hG
  rcases le_total κ μ with h | h
  · exact ⟨μ, hμ, (hF.of_le h).comp hG⟩
  · exact ⟨κ, hκ, hF.comp (hG.of_le h)⟩

lemma isAccessibleFunctor_id (C : SSet.{u + 1}) : IsAccessibleFunctor (𝟙 C) :=
  ⟨Cardinal.aleph0, Cardinal.isRegular_aleph0, isKappaAccessibleFunctor_id _ C⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Def 2.19"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor
attribute [cite HTT "5.4.2.5"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor
attribute [cite HTT "5.4.2.5"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor
attribute [cite HTT "5.4.2.5"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor.of_le
attribute [cite HTT "5.4.2.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor
attribute [cite HTT "5.4.7.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor
attribute [cite HTT "5.5.1.2" (partial := direction) "仮定：accessible C と accessible D への反映 f⊣g、および元の L≃g∘f（HTT の (2) と一致）。結論：f は余極限を保存する左随伴として、g は右随伴として accessible で、その同じ合成 L も accessible（(2)⇒(3) に一致）。L の accessibility だけから像の accessibility を得る逆方向は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor.comp
