module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedEndpointUncurry
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PinchedHomPullbackIso
/-!
概要：引き戻しの入力側の pinched Hom 作用を、元の第二脚の全 join 族として評価する。
方針：引き戻しの端点適合を同じ端点輸送へまとめ、元の後合成を回収する。
規約：全パラメーターと固定終点を保持する。
使われ方：正本標的の底作用を元の導来二作用へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial
variable {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) (v w : (pullback p q) _⦋0⦌)
lemma dgGluingPinchedHomPullbackBaseMap_endpoint :
    pinchedHomPullbackBaseMap p q v w =
    pinchedHomMap q ((pullback.snd p q).app _ v) ((pullback.snd p q).app _ w) ≫
      (pinchedEndpointIso (pullbackSimplex_compat p q v).symm
        (pullbackSimplex_compat p q w).symm).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply PinchedHom.Simplex.ext
  exact (pinchedEndpointIso_hom_val (pullbackSimplex_compat p q v).symm
    (pullbackSimplex_compat p q w).symm (pinchedSimplexMap q a)).symm
lemma dgGluingPinchedHomPullbackBaseMap_evaluation {T : SSet.{u}}
    (h : T ⟶ pinchedHom ((pullback.snd p q).app _ v) ((pullback.snd p q).app _ w)) :
    intervalMappingUncurry (h ≫ pinchedHomPullbackBaseMap p q v w ≫
      pinchedHomToIntervalMappingSpace _ _) =
    rightMappingSpacePrism T ≫ pinchedHomUncurry h ≫ q := by
  rw [dgGluingPinchedHomPullbackBaseMap_endpoint]
  have he := dgGluingPinchedEndpointIso_interval_uncurry
    (pullbackSimplex_compat p q v).symm (pullbackSimplex_compat p q w).symm
    (h ≫ pinchedHomMap q ((pullback.snd p q).app _ v) ((pullback.snd p q).app _ w))
  simpa only [Category.assoc, pinchedHomUncurry_postcomp] using he
end SerrePositivity.InfinityCategories
