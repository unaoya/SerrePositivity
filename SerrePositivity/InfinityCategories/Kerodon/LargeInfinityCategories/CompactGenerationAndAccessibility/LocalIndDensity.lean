module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleDensityLocalColimits

/-!
概要：Ind 同値の標準密度を指定された局所余極限だけで元の圏へ移す。
方針：既存の恒等関手の Hom 普遍性と元の局所左 Kan 構成を使う。
規約：全小余極限の存在は要求しない。
使われ方：一般 accessible 成分の compact 始域密度余錐。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

private lemma homMap_bijective_of_composition
    {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    (R : X ⥤ Y) (T : Y ⥤ Z) (S : X ⥤ Z) (h : S = R ⋙ T)
    (a b : X) (hR : Function.Bijective (fun f : a ⟶ b ↦ R.map f))
    (hT : Function.Bijective (fun f : R.obj a ⟶ R.obj b ↦ T.map f)) :
    Function.Bijective (fun f : a ⟶ b ↦ S.map f) := by
  subst S
  exact hT.comp hR

/-- 概要：Ind 全同値の Yoneda 像の標準密度余錐は指定局所余極限から元の圏で余極限となる。
方針：Ind の filtered 密度による Hom 制限の全単射性を既存の局所左 Kan 判定に渡す。
規約：局所余極限の存在だけを入力にし、元の全小余極限を仮定しない。
使われ方：accessible 性から構成した filtered 局所余極限で密度を閉じる。 -/
lemma indEquivalenceImage_canonicalColimits_of_local_colimits
    {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A) C)
    (hlocal : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ e.hom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ e.hom) ≫ 𝟙 C) y)) :
    ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ e.hom) (𝟙 C) y) := by
  let δ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A
  let i := δ ≫ e.hom
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.canonicalColimits_of_identityRestriction_bijective i hlocal
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

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
