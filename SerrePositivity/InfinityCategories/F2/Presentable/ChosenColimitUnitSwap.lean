module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitParameterApex
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeUnitPrismSwap
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeUnitHomUniversal
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipConstantFunctorHom
public import SerrePositivity.InfinityCategories.F2.Presentable.HomTransportSameEdge

/-!
概要：選んだ余極限関手の全単位を、関手圏内の普遍余錐の単位へ照合する。
方針：全単位円柱の変数交換と元の余錐族の頂点評価を使う。
規約：元の全単位と指定した図式族を保持する。
使われ方：余極限関手と定値関手の随伴の全 Hom 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits SSet.Truncated.HomotopyCategory

/-- 概要：選んだ全単位の変数交換は元のパラメータ普遍余錐の単位。
方針：同じ単位円柱の全一次単体を比較して端点を輸送する。
規約：余極限関手の指定単位を変更しない。
使われ方：随伴の単位 Hom 全単射の構成。 -/
lemma chosenColimitUnit_swap {K A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, HasColimit p) (U : A ⟶ (ihom K).obj X) :
    F1B.kanFunctorHomCongr rfl (flip_postcompose_constant (U ≫ chosenColimitFunctor K X hX))
      (flipFunctorHomEquiv U ((U ≫ chosenColimitFunctor K X hX) ≫ constantFunctorMap K X)
        ((hoFunctor.map ((pre U).app ((ihom K).obj X))).toFunctor.map
          (homMk (functorEdgeOfSimplicialHomotopy (chosenColimitUnit K X hX))))) =
    coconeUnitHom (chosenColimitParameterCocone hX U) ≫
      eqToHom (congrArg (fun z ↦ HomotopyCategory.mk
        (functorVertex (SSet.const z : K ⟶ (ihom A).obj X)))
          (chosenColimitParameterCocone_vertex hX U)) := by
  rw [← functorHomotopyPrecomp_hom]
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    coconeUnitHom, Category.assoc, eqToHom_trans]
  apply homMk_transport_sameEdge rfl
    (congrArg functorVertex (flip_postcompose_constant (U ≫ chosenColimitFunctor K X hX)))
    (congrArg functorVertex (chosenColimitParameterCocone hX U).property)
    (congrArg functorVertex ((cocone_const_rightApex (chosenColimitParameterCocone hX U)).trans
      (congrArg SSet.const (chosenColimitParameterCocone_vertex hX U))))
  change (internalHomSwapIso A K X).hom.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (curry (functorHomotopyPrecomp (chosenColimitUnit K X hX) U).h)) =
      SSet.yonedaEquiv (curry ((coconeDomainHomotopy K).h ≫
        (chosenColimitParameterCocone hX U).val))
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (curry ((U ▷ (Δ[1] : SSet.{u})) ≫
    coconeFunctorUnitPrism (chosenColimitCoconeFamily K X hX)) ≫
      (internalHomSwapIso A K X).hom) = _
  rw [coconeFunctorUnitPrism_precomp, coconeFunctorUnitPrism_swap]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
