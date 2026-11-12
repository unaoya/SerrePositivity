module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomUniversal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftUnitCanonical

/-!
概要：恒等関手を始点とする制限の Hom 全単射性から標準局所密度余錐を構成する。
方針：局所余極限で得た左 Kan 延長と恒等関手を大域普遍性で全自然に比較する。
規約：局所余極限の存在を明示し、大域 Hom 普遍性だけを局所条件と同一視しない。
使われ方：Ind 全同値からの元の compact 模型の密度の回収。

対応節は Kerodon 8.4（Tag 03V7）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion

/-- 概要：恒等関手からの Hom の制限全単射性と局所余極限の存在は標準密度余錐を与える。
方針：実際の左 Kan 延長を作り、大域普遍性の全同型で恒等関手へ戻す。
規約：標準全余錐そのものの余極限性を結論する。
使われ方：小さい compact 生成圏の全密度余錐。 -/
lemma canonicalColimits_of_identityRestriction_bijective
    {K C : SSet.{u}} [Quasicategory K] [Quasicategory C] (i : K ⟶ C)
    (hlocal : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram i (i ≫ 𝟙 C) y))
    (hR : ∀ G : C ⟶ C, Function.Bijective
      (fun η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) G ↦ (hoFunctor.map ((pre i).app C)).toFunctor.map η)) :
    ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone i (𝟙 C) y) := by
  obtain ⟨L, β, hβ, hU⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_with_homUniversal_of_local_colimits
    i (i ≫ 𝟙 C) hlocal
  let R := (hoFunctor.map ((pre i).app C)).toFunctor
  let b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (i ≫ 𝟙 C) (i ≫ L) := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)
  let a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (i ≫ 𝟙 C) (i ≫ 𝟙 C) := 𝟙 _
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal i a := by
    intro G
    change Function.Bijective (fun η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) G ↦ a ≫ R.map η)
    simpa only [a, Category.id_comp] using hR G
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomUniversalIso i b a hU hI
  have hfac : b ≫ R.map e.hom = 𝟙 _ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomUniversalIso_hom_fac i b a hU hI
  have hb : IsIso b := by
    have he : IsIso (R.map e.hom) := inferInstance
    have hbeq : b = inv (R.map e.hom) := by
      calc
        b = b ≫ R.map e.hom ≫ inv (R.map e.hom) := by
          exact (Category.comp_id b).symm.trans
            (congrArg (fun t ↦ b ≫ t) (IsIso.hom_inv_id (R.map e.hom))).symm
        _ = inv (R.map e.hom) := by rw [← Category.assoc, hfac, Category.id_comp]
    rw [hbeq]
    infer_instance
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_canonicalColimits_of_unit_isIso i β hβ hb
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalColimits_of_functorIso i e hL

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
