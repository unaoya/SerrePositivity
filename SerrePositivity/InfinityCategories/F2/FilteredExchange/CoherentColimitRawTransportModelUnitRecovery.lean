module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawTransportModelPreimage

/-!
概要：raw 輸送模型比較と元の余錐単位比較から、元の模型単位比較を厳密に回収する。
方針：元の二 native 因子へ分解し、同じ余錐単位と上側 native 因子を消去する。
規約：元の模型比較・native 表現・単位を保持。使われ方：第一辺合成輸送の指定値の同定。
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
local notation "c" => coconeFiberMap (coherentDiagramTotalCocone F)

/-- 同じ raw 輸送模型比較の単位への像は、a6 の元の模型単位比較そのもの。 -/
lemma coherentColimitRawTransportModelUnitComparison_eq_model :
    coherentColimitRawTransportModelUnitComparison B a =
      coherentColimitIntervalModelUnitComparison B a := by
  have hp := vertexIso_trans_heq_of_heq
    ((coherentColimitRawTransportModelIso B a).precomp c)
    (coherentColimitRawTransportModelUnitFactor B a)
    (coherentColimitModelFiberActionIso B a ≪≫ coherentColimitNativeFiberModelUnitIso B a)
    (coherentColimitRawTransportModelUnitFactor B a)
    (congrArg (fun r => functorVertex (c ≫ r))
      (coherentColimitRawFiberTransport_valueTo B a)) rfl rfl
    (coherentColimitRawTransportModelIso_precomp_heq B a) HEq.rfl
  calc
    _ = (coherentColimitModelFiberActionIso B a ≪≫
        coherentColimitNativeFiberModelUnitIso B a) ≪≫
          coherentColimitRawTransportModelUnitFactor B a :=
      eq_of_heq ((functorIsoOfEq_heq _ _ _).trans hp)
    _ = coherentColimitModelFiberActionIso B a ≪≫
        (coherentColimitUpperNativeFactorIso B a).symm := by
      rw [Iso.trans_assoc, coherentColimitNativeFiberModelUnitIso_cancel]
    _ = _ := coherentColimitModelFiberActionIso_cancel_native B a

end SerrePositivity.InfinityCategories.F2
