module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawTransportModelUnit
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalNativeFiberComparisonImage
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerHEq

/-!
概要：元の native 輸送模型比較と余錐単位比較を合成して、元の上側 native 因子の逆へ戻す。
方針：元の逆像の像を実三頂点で正規化し、同じ単位比較と逆を相殺する。
規約：native 表現・具体的 Kan 射・単位を保持。使われ方：raw 模型単位比較の指定値の回収。
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
local notation "VF" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex F)

/-- 元の native 輸送模型比較の単位での像を、同じ作用始点と固定値終点で読む。 -/
def coherentColimitNativeFiberModelUnitIso :
    FunctorIso (coherentTotalMapNativeAction F G f) (c ≫ (VF ≫ m)) :=
  functorIsoOfEq ((coherentTotalMapNativeFiberTransportIso F G f).precomp c)
    (coherentTotalMapNativeAction_eq F G f).symm
    (congrArg (fun r => c ≫ (r ≫ m)) (coherentTotalSourceValueMap_eq_valueTo F))

/-- 同じ実両端に正規化した native 比較は、元の上側 native 逆因子と単位逆因子の合成。 -/
lemma coherentColimitNativeFiberModelUnitIso_eq_factors :
    coherentColimitNativeFiberModelUnitIso B a =
      (coherentColimitUpperNativeFactorIso B a).symm ≪≫
        (coherentColimitRawTransportModelUnitFactor B a).symm := by
  have hn : HEq (coherentColimitUpperNativeFactorIso B a).symm
      (coherentTotalMapNativeActionIso F G f) := by
    change HEq (functorIsoOfEq (coherentTotalMapNativeActionIso F G f) rfl
      (coherentColimitNativeAction_unit_lift B a)) _
    exact functorIsoOfEq_heq _ _ _
  have hu := functorIso_symm_heq_of_heq ((coherentLargeTotalCoconeUnitIso F).postcomp m)
    (coherentColimitRawTransportModelUnitFactor B a)
    (coherentColimitRawTransportModelUnit_source B a)
    (coherentColimitNativeAction_unit_lift B a) (functorIsoOfEq_heq _ _ _)
  have hp := vertexIso_trans_heq_of_heq
    (coherentColimitUpperNativeFactorIso B a).symm
    (coherentColimitRawTransportModelUnitFactor B a).symm _ _ rfl
    (congrArg functorVertex (coherentColimitNativeAction_unit_lift B a)).symm
    (congrArg functorVertex (coherentColimitRawTransportModelUnit_source B a)).symm hn hu
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    ((coherentTotalMapNativeFiberTransportIso_precomp_heq F G f).trans hp.symm))

/-- 同じ元の単位比較を続けると、上側 native 因子の同じ逆を厳密に回収する。 -/
lemma coherentColimitNativeFiberModelUnitIso_cancel :
    coherentColimitNativeFiberModelUnitIso B a ≪≫
      coherentColimitRawTransportModelUnitFactor B a =
    (coherentColimitUpperNativeFactorIso B a).symm := by
  rw [coherentColimitNativeFiberModelUnitIso_eq_factors]
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end SerrePositivity.InfinityCategories.F2
