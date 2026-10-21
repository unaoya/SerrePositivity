module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitNativeFiberEdge
public import SerrePositivity.InfinityCategories.F2.CoherentColimitSourceValueCast
public import SerrePositivity.InfinityCategories.F2.CoherentTotalMapNativeValueDown

/-!
概要：native 区間表示の Kan 値と a6 の選択済み native Kan 射を同型に比較する。
方針：元の値比較による前合成を反映し、同じ頂点表示で持ち上げた射の同型を降ろす。
規約：指定 native 射と元の表示等式を保持。使われ方：元の全錐の辺の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の native 区間表示の Kan 値は、同じ始域表示を持つ a6 の指定 Kan 射に同型。 -/
def coherentColimitNativeIntervalValueIso : FunctorIso (coherentColimitNativeIntervalValue B H)
    (coherentColimitSourceObjectMap F ≫ coherentTotalMapNativeValueDown F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) := by
  let a := coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)
  let r := coherentTotalSourceValueEquivalence F
  let t := coherentTotalMapNativeFiberTransport F G a ≫
    (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom
  have en := r.homInvIso.postcomp t
  have hn : FunctorIso (coherentTotalSourceValueMap F ≫ coherentTotalMapNativeValue F G a) t := by
    have hr : r.hom = coherentTotalSourceValueMap F := rfl
    refine functorIsoOfEq en ?_ (Category.id_comp t)
    rw [hr]
    rfl
  have e := coherentColimitNativeIntervalLiftIso B H ≪≫ hn.symm
  have ht : coherentTotalSourceValueMap F ≫ coherentTotalMapNativeValue F G a =
      (pointedSpaceFiberValueEquivalence (coherentDiagramTotalCocone F).vertex).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentColimitSourceObjectMap F ≫ coherentTotalMapNativeValueDown F G a) := by
    rw [coherentColimitSourceValueMap_eq, Functor.map_comp, coherentTotalMapNativeValueDown_lift]
    exact Category.assoc _ _ _
  have he := functorIsoOfEq e rfl ht
  have hp := ((pointedSpaceFiberValueEquivalence (coherentDiagramTotalCocone F).vertex).precompose
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (spaceInfinityObject (coherentDiagramTotalVertex G)).obj)).isQCatEquivalence
  exact functorIsoDown (hp.isFullyFaithful.preimageVertexIso he)

/-- 元の余極限関手の指定辺の Kan 値は、元の上下二単体を介して a6 の指定射に同型。 -/
def coherentColimitEdgeValueIso : FunctorIso (coherentColimitEdgeValue B H)
    (coherentColimitSourceObjectMap F ≫ coherentTotalMapNativeValueDown F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) :=
  coherentColimitEdgeValueNativeIso B H ≪≫ coherentColimitNativeIntervalValueIso B H

end SerrePositivity.InfinityCategories.F2
