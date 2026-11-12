module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitModelFiberActionImage
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompEndpointTransport

/-!
概要：raw 輸送模型比較の単位での像を、同じ元の二つの native 比較へ分解する。
方針：前合成の合成保存と、元の三実頂点の表示変更を使う。
規約：a6 の選択済み二比較を保持。使われ方：元の模型単位比較の指定値の回収。
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
local notation "f" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy a)
local notation "m" => CategoryTheory.Functor.map SSet.uliftFunctor (coherentTotalVertexMap F G f)
local notation "c" => coconeFiberMap (coherentDiagramTotalCocone F)

/-- 元の raw 模型比較の単位での像は、同じ a6 fiber 比較と native 模型比較の合成。 -/
lemma coherentColimitRawTransportModelIso_precomp_heq :
    HEq ((coherentColimitRawTransportModelIso B a).precomp c)
      (coherentColimitModelFiberActionIso B a ≪≫ coherentColimitNativeFiberModelUnitIso B a) := by
  have hr := functorIsoOfEq_precomp_heq
    (coherentColimitFiberTransportComparisonIso B a ≪≫
      coherentTotalMapNativeFiberTransportIso F G f)
    (coherentColimitRawFiberTransport_valueTo B a).symm
    (congrArg (fun r => r ≫ m) (coherentTotalSourceValueMap_eq_valueTo F)) c
  have hn := vertexIso_trans_heq_of_heq
    (coherentColimitModelFiberActionIso B a) (coherentColimitNativeFiberModelUnitIso B a)
    ((coherentColimitFiberTransportComparisonIso B a).precomp c)
    ((coherentTotalMapNativeFiberTransportIso F G f).precomp c) rfl
    (congrArg functorVertex (coherentTotalMapNativeAction_eq F G f))
    (congrArg (fun r => functorVertex (c ≫ (r ≫ m)))
      (coherentTotalSourceValueMap_eq_valueTo F)).symm
    (functorIsoOfEq_heq _ _ _) (functorIsoOfEq_heq _ _ _)
  exact hr.trans ((heq_of_eq (functorIso_precomp_trans _ _ c)).trans hn.symm)

end SerrePositivity.InfinityCategories.F2
