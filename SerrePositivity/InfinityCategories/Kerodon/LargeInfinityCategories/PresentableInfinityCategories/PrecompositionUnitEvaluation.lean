module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TransposeHomEvaluation

/-!
概要：前合成の Hom 対応を恒等関手で評価して元の単位成分へ戻す。
方針：転置後の評価の可換性と端点輸送の合成を計算する。
規約：元の全関手圏と指定単位の Hom を保持する。
使われ方：固定左 coslice の始対象性と元の随伴単位条件の照合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomMap

/-- 概要：恒等関手を点として二重関手圏を元の圏へ評価する。
方針：元の C 上の恒等関手頂点で評価する。
規約：全ての単体に作用する元の評価射。
使われ方：前合成の単位を元の単位へ戻す評価。 -/
abbrev identityFunctorEvaluation (C : SSet.{u}) :
    (ihom ((ihom C).obj C)).obj C ⟶ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C))

/-- 概要：前合成の Hom 対応の出口を恒等関手で評価すると元の単位成分になる。
方針：端点輸送を評価の後へ移し、転置 Hom の評価公式を適用する。
規約：単位候補に随伴条件は要求しない。
使われ方：前合成随伴の単位成分の回収の出口側。 -/
lemma precompositionTargetEquiv_unit_evaluate {C D : SSet.{u}} [Quasicategory C]
    (L : C ⟶ D) (R : D ⟶ C)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 ((ihom C).obj C)) ((pre R).app C ≫ (pre L).app C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (A := C) (D := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeIdentity_evaluate C)
      (congrArg (L ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposePre_evaluate R))
      ((hoFunctor.map ((ihom C).map (identityFunctorEvaluation C))).toFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv (Z := C) L (𝟙 ((ihom C).obj C)) ((pre R).app C) η)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent (F := (pre R).app C) (G := (pre L).app C) η
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) := by
  change _ = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv, Equiv.trans_apply]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_postcomp (identityFunctorEvaluation C) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := C) L ((pre R).app C))]
  let τ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose (𝟙 ((ihom C).obj C)) ≫ identityFunctorEvaluation C)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose ((pre R).app C ≫ (pre L).app C) ≫ identityFunctorEvaluation C) :=
    (hoFunctor.map ((ihom C).map (identityFunctorEvaluation C))).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (Z := C) (𝟙 ((ihom C).obj C)) ((pre R).app C ≫ (pre L).app C) η)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeIdentity_evaluate C)
    (congrArg (L ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposePre_evaluate R))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr rfl
      (congrArg (· ≫ identityFunctorEvaluation C)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := C) L ((pre R).app C))) τ) = _
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_trans (A := C) (E := C) rfl
    (congrArg (· ≫ identityFunctorEvaluation C)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := C) L ((pre R).app C)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeIdentity_evaluate C) (congrArg (L ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposePre_evaluate R)) τ).trans ?_
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_evaluate η (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
