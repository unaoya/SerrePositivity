module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrecompositionSourceEvaluation

/-!
概要：前合成の全 QCat 随伴の単位を恒等関手で評価して元の単位を回収する。
方針：転置した Hom 対応の入口・出口の評価と Hom₁ の後合成自然性をつなぐ。
規約：元の左右の関手と指定された随伴の単位を保持する。
使われ方：固定左の普遍単位と元の随伴単位条件の照合。

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

/-- 概要：前合成の随伴単位の恒等関手での成分は元の随伴単位。
方針：Hom 対応の単位構成を評価し、元の Hom₁ 逆対応の恒等射の公式へ戻す。
規約：元の h Fun(C,C) の指定単位を厳密に回収する。
使われ方：元の実単位に対する固定左 coslice の始対象性の証明。 -/
lemma precompositionAdjunction_unitComponent_identity {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent (F := (pre R).app C) (G := (pre L).app C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionAdjunction (Z := C) a).unitHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) = a.unitHom := by
  let X := (ihom C).obj C
  let U := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose (𝟙 X)
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose ((pre R).app C)
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.identityFunctorEvaluation C
  let β := 𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre R).app C)))
  let η := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionAdjunction (Z := C) a).unitHom
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionSourceEquiv (Z := C) R (𝟙 X) ((pre R).app C) β
  have hU : U ≫ k = 𝟙 C := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeIdentity_evaluate C
  have hV : V ≫ k = R := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposePre_evaluate R
  let normalize : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (L ≫ V) → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) (L ≫ R) := fun γ ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (A := C) (D := C) hU (congrArg (L ≫ ·) hV)
      ((hoFunctor.map ((ihom C).map k)).toFunctor.map γ)
  have hη : η = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv (Z := C) a (𝟙 X) ((pre R).app C) β := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionAdjunction_unitHom (Z := C) a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionUnitArgument (Z := C) R] at h
    exact h
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv_formula (Z := C) a (𝟙 X) ((pre R).app C) β
  rw [← hη] at hc
  have he := congrArg normalize hc
  have ht : normalize (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv (Z := C) L (𝟙 X) ((pre R).app C) η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent (F := (pre R).app C) (G := (pre L).app C) η
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv_unit_evaluate L R η
  let σ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ (U ≫ k)) (V ≫ k) :=
    (hoFunctor.map ((ihom D).map k)).toFunctor.map s
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv_postcomp a s k
  have hm' := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU (congrArg (L ≫ ·) hV)) hm
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv_congr a hU hV σ
  have hnorm := hm'.symm.trans hn
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (congrArg (R ≫ ·) hU) hV σ =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R)) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionSourceEquiv_unit_evaluate R
  have hlast := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a (𝟙 C) R) hs
  exact ht.symm.trans
    (he.trans (hnorm.trans (hlast.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv_identity a))))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
