module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalSourceValueTo
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawTransportPointPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitFiberTransportImage

/-!
概要：元の raw 輸送を、a6 の同じ選択済み比較によって元の具体的 Kan 頂点射へ写す。
方針：raw/native の実値射の等式と、元の二つの指定輸送比較を合成する。
規約：元の区間比較・native 表現・具体的頂点射を保持。使われ方：三角形と全錐の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "m" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy a)
local notation "VF" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex F)
local notation "VG" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)
local notation "W" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G))

/-- 元の raw 輸送と元の具体的 Kan 頂点射を、同じ二つの選択済み比較で結ぶ指定同型。 -/
def coherentColimitRawTransportModelIso :
    FunctorIso (coherentColimitRawFiberTransport B a ≫ VG)
      (VF ≫ (SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G m)) :=
  functorIsoOfEq
    (coherentColimitFiberTransportComparisonIso B a ≪≫
      coherentTotalMapNativeFiberTransportIso F G m)
    (coherentColimitRawFiberTransport_valueTo B a).symm
    (congrArg (fun f => f ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (coherentTotalVertexMap F G m)) (coherentTotalSourceValueMap_eq_valueTo F))

/-- 同じ raw 表示への変更は、a6 の元の輸送比較と元の native 比較の指定合成を保つ。 -/
lemma coherentColimitRawTransportModelIso_heq_native :
    HEq (coherentColimitRawTransportModelIso B a)
      (coherentColimitFiberTransportComparisonIso B a ≪≫
      coherentTotalMapNativeFiberTransportIso F G m) :=
  functorIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories.F2
