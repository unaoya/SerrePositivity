module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrecompositionCorrespondence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomTransportNaturality

/-!
概要：前合成の Hom 対応の全パラメータ自然性。
方針：転置の始域自然性と端点輸送を組み合わせる。
規約：元の関手単体集合上の全てのパラメータの射を扱う。
使われ方：前合成の全 QCat 随伴への接続。

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

/-- 概要：前合成の Hom 対応の入口はパラメータの制限と可換。
方針：転置の第一始域自然性に、右関手による前合成への端点輸送を適用する。
規約：元の全関手圏の任意の Hom を保持する。
使われ方：前合成随伴のパラメータ自然性。 -/
lemma precompositionSourceEquiv_parameter {A₀ A C D Z : SSet.{u}} [Quasicategory Z]
    (i : A₀ ⟶ A) (R : D ⟶ C)
    (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr
      (congrArg (R ≫ ·) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i U))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionSourceEquiv (Z := Z) R (i ≫ U) (i ≫ V)
        ((hoFunctor.map ((pre i).app ((ihom D).obj Z))).toFunctor.map α)) =
    (hoFunctor.map ((ihom D).map ((pre i).app Z))).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionSourceEquiv (Z := Z) R U V α) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionSourceEquiv, Equiv.trans_apply]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceHomTransportEquiv_eq_congr]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_postcomp ((pre i).app Z)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) R U) rfl]
  have h := congrArg
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr
      (congrArg (· ≫ (pre i).app Z) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) R U)) rfl)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_pre_left (Z := Z) i α)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_trans] at h ⊢
  (convert h using 1; rfl)

/-- 概要：前合成の Hom 対応の出口はパラメータの制限と可換。
方針：転置の第一始域自然性に、左関手による前合成への端点輸送を適用する。
規約：元の全関手圏の任意の Hom を保持する。
使われ方：前合成随伴のパラメータ自然性。 -/
lemma precompositionTargetEquiv_parameter {A₀ A C D Z : SSet.{u}} [Quasicategory Z]
    (i : A₀ ⟶ A) (L : C ⟶ D)
    (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ (pre L).app Z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i U)
      (congrArg (L ≫ ·) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i V))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv (Z := Z) L (i ≫ U) (i ≫ V)
        ((hoFunctor.map ((pre i).app ((ihom C).obj Z))).toFunctor.map α)) =
    (hoFunctor.map ((ihom C).map ((pre i).app Z))).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv (Z := Z) L U V α) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv, Equiv.trans_apply]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_postcomp ((pre i).app Z)
    rfl (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) L V)]
  have h := congrArg
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr rfl
      (congrArg (· ≫ (pre i).app Z) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) L V)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_pre_left (Z := Z) i α)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_trans] at h ⊢
  (convert h using 1; rfl)

/-- 概要：前合成の Hom 対応は全パラメータの制限に自然。
方針：入口・出口の転置自然性の間で Hom₁ の後合成自然性を適用する。
規約：パラメータの充填性は要求しない。
使われ方：全 QCat 随伴の自然な Hom 対応。 -/
lemma precompositionTransposeEquiv_parameter {A₀ A C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (i : A₀ ⟶ A) (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv (Z := Z) a (i ≫ U) (i ≫ V)
      ((hoFunctor.map ((pre i).app ((ihom D).obj Z))).toFunctor.map α) =
    (hoFunctor.map ((pre i).app ((ihom C).obj Z))).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv (Z := Z) a U V α) := by
  apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv (Z := Z) L (i ≫ U) (i ≫ V)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i U)
      (congrArg (L ≫ ·) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i V)))).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i U)
      (congrArg (L ≫ ·) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i V))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv (Z := Z) L (i ≫ U) (i ≫ V) _) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i U)
      (congrArg (L ≫ ·) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i V))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTargetEquiv (Z := Z) L (i ≫ U) (i ≫ V) _)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv_formula (Z := Z),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv_congr a (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i U)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left (D := Z) i V),
    precompositionSourceEquiv_parameter (Z := Z), precompositionTargetEquiv_parameter (Z := Z),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv_formula (Z := Z), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv_postcomp]

/-- 概要：右・左随伴による前合成の自然な全パラメータ Hom 対応。
方針：転置した Hom₁ 逆対応と三つの自然性をまとめる。
規約：元の全関手単体集合を使う。
使われ方：前合成の全 QCat 随伴の構成。 -/
def precompositionCorrespondence {C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence ((pre R).app Z) ((pre L).app Z) where
  equiv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv (Z := Z) a
  naturality_right := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv_comp (Z := Z) a
  naturality_left := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv_precomp (Z := Z) a
  precomp := precompositionTransposeEquiv_parameter (Z := Z) a

/-- 概要：元の随伴は内部 Hom の前合成による全 QCat 随伴を与える。
方針：全パラメータに自然な Hom 全単射から単位・余単位と三角恒等式を構成する。
規約：関手単体集合をホモトピー圏に置き換えず、追加の存在仮定も使わない。
使われ方：左射影の固定ファイバーを普遍単位の空間として計算する。 -/
def precompositionAdjunction {C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction ((pre R).app Z) ((pre L).app Z) :=
  (precompositionCorrespondence (Z := Z) a).toAdjunction

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
