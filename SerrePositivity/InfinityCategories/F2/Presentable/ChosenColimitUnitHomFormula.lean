module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitUnitSwap
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipUnitHomFormula
public import SerrePositivity.InfinityCategories.HomotopyLimits.ParameterUnitHom

/-!
概要：選んだ余極限単位の全 Hom 写像を普遍余錐の単位 Hom 写像へ移す。
方針：変数交換の合成保存と全単位の照合を使う。
規約：同じ指定単位と元のパラメータ付き二関手を保持する。
使われ方：余極限関手と定値関手の随伴の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits SSet.Truncated.HomotopyCategory

/-- 概要：選んだ余極限関手の指定単位の Hom 類。
方針：同じ全単位の代表辺をホモトピー圏へ写す。
規約：単位の選択を変更しない。
使われ方：全パラメータの随伴判定。 -/
def chosenColimitUnitHom (K X : SSet.{u}) [Quasicategory X]
    (hX : ∀ p : K ⟶ X, HasColimit p) :
    FunctorHom (𝟙 ((ihom K).obj X))
      (chosenColimitFunctor K X hX ≫ constantFunctorMap K X) :=
  homMk (functorEdgeOfSimplicialHomotopy (chosenColimitUnit K X hX))

/-- 概要：指定単位の Hom 写像の転置は native な普遍余錐の Hom 写像。
方針：単位と後合成の転置を別々に照合して合成する。
規約：元の二関手と指定した射を保つ。
使われ方：単位の全 Hom 全単射性。 -/
lemma chosenColimitUnitHomMap_flip {K A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, HasColimit p) (U : A ⟶ (ihom K).obj X) (V : A ⟶ X)
    (α : FunctorHom (U ≫ chosenColimitFunctor K X hX) V) :
    F1B.kanFunctorHomCongr rfl (flip_postcompose_constant V)
      (flipFunctorHomEquiv U (V ≫ constantFunctorMap K X)
        (parameterUnitHomMap (chosenColimitUnitHom K X hX) U V α)) =
    coconeUnitHom (chosenColimitParameterCocone hX U) ≫ constantFunctorHomMap K
      (eqToHom (congrArg HomotopyCategory.mk (chosenColimitParameterCocone_vertex hX U)) ≫ α) :=
  flip_composite_constant_hom_of_unit
    (U := U) (L := U ≫ chosenColimitFunctor K X hX) (V := V)
    ((hoFunctor.map ((pre U).app ((ihom K).obj X))).toFunctor.map
      (chosenColimitUnitHom K X hX))
    (coconeUnitHom (chosenColimitParameterCocone hX U))
    (chosenColimitParameterCocone_vertex hX U) (chosenColimitUnit_swap hX U) α

end SerrePositivity.InfinityCategories.F2.Presentable
