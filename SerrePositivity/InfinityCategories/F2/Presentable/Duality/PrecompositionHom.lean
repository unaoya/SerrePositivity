module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.AdjointVertices
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorTranspose

/-!
概要：元の随伴が前合成で与える、任意のパラメータ上の Hom 全単射を構成する。
方針：内部 Hom の二変数を転置し、元の双圏随伴のもう一方の Hom 対応を使う。
規約：元の関手圏全体を使い、ホモトピー圏の対象間の Hom だけに制限しない。
使われ方：左右の mate 写像の全パラメータの両逆を検証する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

local instance precompositionHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：二重内部 Hom の転置は元の二胞体の Hom 全単射を与える。
方針：内部 Hom の交換同型による h での充満忠実性を適用する。
規約：A・B の充填性は要求せず、標的 Z だけを quasicategory とする。
使われ方：前合成の Hom 対応を元の随伴の型に移す。 -/
def transposeHomEquiv {A B Z : SSet.{u}} [Quasicategory Z]
    (U V : A ⟶ (ihom B).obj Z) :
    FunctorHom U V ≃ FunctorHom (F1B.functorTranspose U) (F1B.functorTranspose V) :=
  (qCatEquivalenceOfIso (internalHomSwapIso A B Z)).isFullyFaithful.toHoFullyFaithful.homEquiv
    (X := HomotopyCategory.mk (functorVertex U)) (Y := HomotopyCategory.mk (functorVertex V))

/-- 概要：右関手による前合成の Hom は左関手による前合成の Hom と全単射。
方針：二つの転置の間に、元の随伴の Hom₁ の逆対応を挟む。
規約：パラメータ A は任意、U・V も定値関手に限らない。
使われ方：随伴の mate の全高次単体の比較に使う全パラメータの判定。 -/
def precompositionHomEquiv {A C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : QCatAdjunction L R)
    (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z) :
    FunctorHom (U ≫ (pre R).app Z) V ≃ FunctorHom U (V ≫ (pre L).app Z) := by
  let U' := F1B.functorTranspose U
  let V' := F1B.functorTranspose V
  have e₁ : FunctorHom (U ≫ (pre R).app Z) V ≃ FunctorHom (R ≫ U') V' := by
    simpa only [F1B.functorTranspose_pre_right, U', V'] using
      transposeHomEquiv (U ≫ (pre R).app Z) V
  have e₂ : FunctorHom (R ≫ U') V' ≃ FunctorHom U' (L ≫ V') :=
    (qcatCellEquiv (R ≫ U') V').symm.trans
      ((Bicategory.Adjunction.homEquiv₁ a (g := qcatMap U') (h := qcatMap V')).symm.trans
        (qcatCellEquiv U' (L ≫ V')))
  have e₃ : FunctorHom U (V ≫ (pre L).app Z) ≃ FunctorHom U' (L ≫ V') := by
    simpa only [F1B.functorTranspose_pre_right, U', V'] using
      transposeHomEquiv U (V ≫ (pre L).app Z)
  exact e₁.trans (e₂.trans e₃.symm)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
