module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointVertices
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTranspose

/-!
概要：元の随伴が前合成で与える、任意のパラメータ上の Hom 全単射を構成する。
方針：内部 Hom の二変数を転置し、元の双圏随伴のもう一方の Hom 対応を使う。
規約：元の関手圏全体を使い、ホモトピー圏の対象間の Hom だけに制限しない。
使われ方：左右の mate 写像の全パラメータの両逆を検証する入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance precompositionHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：二重内部 Hom の交換を元の Hom の射に作用させる。
方針：交換射が h に誘導する関手の射作用を使う。
規約：転置後の元の関手頂点を戻り値の型として明示する。
使われ方：全単射の内部構成を展開しない転置 Hom の型付き界面。 -/
def transposeHomMap {A B Z : SSet.{u}} [Quasicategory Z]
    (U V : A ⟶ (ihom B).obj Z) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V) :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B Z).hom).toFunctor.map
    (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
    (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) α

/-- 概要：二重内部 Hom の転置は元の二胞体の Hom 全単射を与える。
方針：交換射の h での直接の射作用に、交換同型の充満忠実性を適用する。
規約：A・B の充填性は要求せず、標的 Z だけを quasicategory とする。
使われ方：前合成の Hom 対応を元の随伴の型に移す。 -/
def transposeHomEquiv {A B Z : SSet.{u}} [Quasicategory Z]
    (U V : A ⟶ (ihom B).obj Z) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V) :=
  Equiv.ofBijective (transposeHomMap U V)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B Z)).isFullyFaithful.toHoFullyFaithful.homEquiv
      (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
      (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V))).bijective

/-- 概要：右関手による前合成の Hom は左関手による前合成の Hom と全単射。
方針：二つの転置の間に、元の随伴の Hom₁ の逆対応を挟む。
規約：パラメータ A は任意、U・V も定値関手に限らない。
使われ方：随伴の mate の全高次単体の比較に使う全パラメータの判定。 -/
def precompositionHomEquiv {A C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ (pre L).app Z) := by
  let U' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U
  let V' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V
  have e₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ U') V' := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right, U', V'] using
      transposeHomEquiv (U ≫ (pre R).app Z) V
  have e₂ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ U') V' ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' (L ≫ V') :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (R ≫ U') V').symm.trans
      ((Bicategory.Adjunction.homEquiv₁ a (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U') (h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V')).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U' (L ≫ V')))
  have e₃ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ (pre L).app Z) ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' (L ≫ V') := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right, U', V'] using
      transposeHomEquiv U (V ≫ (pre L).app Z)
  exact e₁.trans (e₂.trans e₃.symm)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
