module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalMapNativeTransport

/-!
概要：native 余極限写像の値を元の具体的な Kan 頂点射へ比較する。
方針：始域 fiber の値比較の逆を使い、元の輸送比較と逆同値の余単位を合成する。
規約：選択済み native 射と元の頂点射を保持。使われ方：引き戻し交換の二脚の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)

/-- 概要：元の始域 fiber の値比較に、選択した逆と両合成同型を添える。
方針：元の比較射の同値性。規約：順方向は元の比較。使われ方：輸送の値への移送。 -/
def coherentTotalSourceValueEquivalence :=
  (coherentTotalSourceValueMap_isQCatEquivalence F).choose

/-- 概要：選択済み native 余極限写像の実際の輸送を両頂点の元の値の間で表示。
方針：元の fiber 輸送を始域・終域の値比較で挟む。
規約：値の宇宙は持ち上げたまま。使われ方：具体的 Kan 頂点射との照合。 -/
def coherentTotalMapNativeValue :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (coherentDiagramTotalVertex F)).obj ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (coherentDiagramTotalVertex G)).obj :=
  (coherentTotalSourceValueEquivalence F).inv ≫ coherentTotalMapNativeFiberTransport F G a ≫
    (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom

/-- 概要：元の native 写像の値は元の具体的 Kan 頂点射の持ち上げと同型。
方針：元の輸送の指定比較を値比較の逆で制限し、余単位を続ける。
規約：元の具体的な射を保持。使われ方：元の Kan 極限錐と native 余極限の二脚の比較。 -/
def coherentTotalMapNativeValueIso :
    FunctorIso (coherentTotalMapNativeValue F G a)
      ((SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a)) := by
  let r := coherentTotalSourceValueEquivalence F
  let m := (SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a)
  have e := (coherentTotalMapNativeFiberTransportIso F G a).precomp r.inv
  have h := r.invHomIso.postcomp m
  have h' : FunctorIso (r.inv ≫ (r.hom ≫ m)) m := by
    simpa only [Category.assoc, Category.id_comp] using h
  exact e ≪≫ h'

end SerrePositivity.InfinityCategories.F2
