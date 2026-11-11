module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.DenseCanonicalColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallLeftKanModels
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratorEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndContinuousLeftKan

/-!
概要：Ind 同値で写した元の Yoneda 生成圏の標準密度余錐を、元の圏内で構成する。
方針：同値による前合成と Ind の密度の Hom 全単射を合成し、実際の局所余極限で戻す。
規約：元の圏の局所小ささと小余極限を明示する。
使われ方：全 compact 小模型による標準余錐の余極限性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

private lemma homMap_bijective_of_composition
    {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    (R : X ⥤ Y) (T : Y ⥤ Z) (S : X ⥤ Z) (h : S = R ⋙ T)
    (a b : X) (hR : Function.Bijective (fun f : a ⟶ b ↦ R.map f))
    (hT : Function.Bijective (fun f : R.obj a ⟶ R.obj b ↦ T.map f)) :
    Function.Bijective (fun f : a ⟶ b ↦ S.map f) := by
  subst S
  exact hT.comp hR

/-- 概要：Ind 全同値の Yoneda 像に沿う標準密度余錐は元の圏の余極限。
方針：恒等関手からの Hom の制限を二つの全単射の合成として判定する。
規約：同値の像の点だけでなく元の任意の頂点について結論する。
使われ方：compact 小模型の全標準密度余錐。 -/
lemma indEquivalenceImage_canonicalColimits
    {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall C)
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A) C) :
    ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ e.hom) (𝟙 C) y) := by
  let δ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A
  let i := δ ≫ e.hom
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.canonicalColimits_of_identityRestriction_bijective i
    (fun y ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_leftKanDiagram_of_locallySmall hC hcol i (i ≫ 𝟙 C) y)
  intro G
  let R := (hoFunctor.map ((pre e.hom).app C)).toFunctor
  let T := (hoFunctor.map ((pre δ).app C)).toFunctor
  let S := (hoFunctor.map ((pre i).app C)).toFunctor
  have hS : S = R ⋙ T := by
    dsimp only [S, R, T, i]
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  have hR := (e.isQCatEquivalence.isPrecompositionEquivalence C).choose.isFullyFaithful.toHoFullyFaithful
  have hcontinuous : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (e.hom ≫ 𝟙 C) := by
    intro I hI hfiltered D c hc
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc
  have hT := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHomMap_bijective δ (e.hom ≫ 𝟙 C)
    (fun y ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indContinuous_canonicalColimits μ (e.hom ≫ 𝟙 C) y hcontinuous) (e.hom ≫ G)
  exact homMap_bijective_of_composition R T S hS
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C))) (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (hR.map_bijective _ _) hT

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
