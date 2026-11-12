module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AdjunctionLimits

/-!
概要：局所輸送同定の下で、実 U の任意 coherent ∞ 極限保存を証明する。
方針：同じ条件から構成した全 ∞ 随伴に、公開された極限錐保存定理を適用する。
規約：図式の形状 K は任意。同じ U と元の指定極限錐を保持する。
使われ方：P-6 の代入後の g2-4 と、既存 CAlg_R による G1′ の極限保存入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

lemma cAlgForgetDerived_mapJoinCone_isLimit_of_transport
    (h : FreeProbeUnitTransportCondition A) {K : SSet.{u + 1}} {p : K ⟶ CAlg_R A}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (cAlgForgetDerived A) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction (cAlgFreeForgetDerivedAdjunctionOfTransport A h) c hc

lemma cAlgForgetDerived_hasLimit_postcomp_of_transport
    (h : FreeProbeUnitTransportCondition A) {K : SSet.{u + 1}} (p : K ⟶ CAlg_R A)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (p ≫ cAlgForgetDerived A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_postcomp_of_adjunction (cAlgFreeForgetDerivedAdjunctionOfTransport A h) p hp

end SerrePositivity.EInfinity.BarrattEccles
