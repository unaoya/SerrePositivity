module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitNativeFiberUnitCancellation
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUpperNativeCancellation

/-!
概要：a6 の元の fiber 比較の余錐での像を、同じ作用終点で回収する。
方針：実終点の式だけを揃え、元の作用比較と上側 native 逆因子の消去式を用いる。
規約：選択済み fiber 比較と模型比較を保持。使われ方：raw 模型単位比較の像の照合。
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
local notation "c" => coconeFiberMap (coherentDiagramTotalCocone F)

/-- a6 の元の fiber 比較の単位での像を、元の native 作用を終点にして保持する。 -/
def coherentColimitModelFiberActionIso :=
  functorIsoOfEq ((coherentColimitFiberTransportComparisonIso B a).precomp c) rfl
    (coherentTotalMapNativeAction_eq F G f).symm

/-- 同じ実終点への表示変更は、元の上下作用比較の指定合成を回収する。 -/
lemma coherentColimitModelFiberActionIso_eq_actions :
    coherentColimitModelFiberActionIso B a =
      (coherentColimitLowerActionIso B a).symm ≪≫ coherentColimitUpperActionIso B a :=
  eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    (coherentColimitFiberTransportComparisonIso_precomp_heq B a))

/-- 同じ上側 native 逆因子を続けると、元の模型単位比較が厳密に回収される。 -/
lemma coherentColimitModelFiberActionIso_cancel_native :
    coherentColimitModelFiberActionIso B a ≪≫
      (coherentColimitUpperNativeFactorIso B a).symm =
    coherentColimitIntervalModelUnitComparison B a := by
  rw [coherentColimitModelFiberActionIso_eq_actions,
    coherentColimitActionComparison_cancel_upperNative]
  exact (coherentColimitIntervalModelUnitComparison_eq_reduced B a).symm

end SerrePositivity.InfinityCategories.F2
