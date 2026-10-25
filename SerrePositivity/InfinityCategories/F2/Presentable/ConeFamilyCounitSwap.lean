module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConeFamilyAdjunct
public import SerrePositivity.InfinityCategories.F2.Presentable.ConeCounitHomUniversal
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeUnitPrismSwap
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipConstantFunctorHom
public import SerrePositivity.InfinityCategories.F2.Presentable.HomTransportSameEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LimitConeFamilyFunctor

/-!
概要：全錐族の指定余単位の変数交換を、関手圏内の native な錐の余単位へ照合する。
方針：二重 curry の一般公式で全円柱を比較し、共通の端点へ輸送する。
規約：同じ一次単体と全パラメータを保持する。
使われ方：全極限錐族と極限関手の自然比較の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全余単位円柱の変数交換は元の錐形状ホモトピーの像。
方針：形状円柱についての一般の二重 curry の交換公式を適用する。
規約：全次数のパラメータを保持する。
使われ方：元の全余単位と native な錐の余単位の代表の照合。 -/
lemma coneFunctorCounitPrism_swap {A K X : SSet.{u}}
    (s : A ⟶ (ihom (join Δ[0] K)).obj X) :
    curry (coneFunctorCounitPrism s) ≫ (internalHomSwapIso A K X).hom =
      curry ((coneDomainHomotopy K).h ≫ internalHomFlipHomEquiv A (join Δ[0] K) X s) :=
  coconeUnitReorder_curry_swap (coneDomainHomotopy K).h s

/-- 概要：全錐族の余単位の転置は、同じ関手圏内の錐の余単位。
方針：元の代表一次単体の等式を共通の端点へ輸送する。
規約：錐の頂点の表示の等式を明示する。
使われ方：随伴による比較の全 Hom 普遍性。 -/
lemma coneFamilyCounitHom_swap {A K X : SSet.{u}} [Quasicategory X]
    (s : A ⟶ (ihom (join Δ[0] K)).obj X) :
    F1B.kanFunctorHomCongr
      (flip_postcompose_constant
        (s ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInl Δ[0] K)))) rfl
      (flipFunctorHomEquiv _ _ (coneFunctorCounitHom s)) =
    F1B.kanFunctorHomCongr
      (congrArg SSet.const (pointwiseLimitFamilyCone_vertex s)) rfl
      (coneCounitHom (pointwiseLimitFamilyCone s)) := by
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    coneCounitHom, coneFunctorCounitHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  refine homMk_transport_sameEdge
    (congrArg functorVertex (flip_postcompose_constant
      (s ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInl Δ[0] K))))) rfl
    (congrArg functorVertex ((SSet.const_comp
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))
      (pointwiseLimitFamilyCone s).val).trans
        (congrArg SSet.const (pointwiseLimitFamilyCone_vertex s))))
    (congrArg functorVertex (pointwiseLimitFamilyCone s).property)
    ((functorEdgeOfSimplicialHomotopy (coneFunctorCounitHomotopy s)).map
      ((truncation 2).map (internalHomSwapIso A K X).hom))
    (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (coneDomainHomotopy K) (pointwiseLimitFamilyCone s).val)) ?_
  change (internalHomSwapIso A K X).hom.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (curry (coneFunctorCounitPrism s))) =
    SSet.yonedaEquiv (curry ((coneDomainHomotopy K).h ≫ (pointwiseLimitFamilyCone s).val))
  rw [← SSet.yonedaEquiv_comp, coneFunctorCounitPrism_swap]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
