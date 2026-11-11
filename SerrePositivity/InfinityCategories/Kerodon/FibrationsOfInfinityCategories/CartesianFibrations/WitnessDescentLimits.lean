module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessColimitDescent

/-!
概要：底上の表現空間の反変関手は小さい反対形状の極限を保つ。
方針：極限錐を底上の余極限錐へ戻して降下定理を適用する。
規約：添字とその反対を明示して反変性を保つ。
使われ方：底の骨格列の表現空間を逆極限で計算する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：実際の表現空間の反変関手は小さい反対形状の極限を保つ。
方針：極限錐の反対の余極限錐に表現の降下を適用する。
規約：単体集合の宇宙で小さい添字を扱う。
使われ方：骨格列の余極限を表現空間の逆極限へ移す。 -/
instance transportWitnessPullbackFunctor_preservesLimitsOfShape_op {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (J : Type v) [Category.{w} J] [Small.{u + 1} J] :
    PreservesLimitsOfShape Jᵒᵖ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p) where
  preservesLimit {K} := by
    refine { preserves := ?_ }
    intro c hc
    change Cone K.unop.op at c
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessColimitCone_isLimit p c.unop hc.unop
    exact ⟨IsLimit.ofIsoLimit h (Cone.ext (Iso.refl _) (by intro j; rfl))⟩

/-- 概要：実際の表現空間の反変関手は任意の小さい形状の極限を保つ。
方針：反対形状の極限保存を二重反対圏との同値で移す。
規約：モデル構造や表現の存在を仮定しない。
使われ方：非交和・pushout・骨格列の統一した極限の界面。 -/
instance transportWitnessPullbackFunctor_preservesLimitsOfShape {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (J : Type v) [Category.{w} J] [Small.{u + 1} J] :
    PreservesLimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p) := by
  let := transportWitnessPullbackFunctor_preservesLimitsOfShape_op p Jᵒᵖ
  exact preservesLimitsOfShape_of_equiv (opOpEquivalence J) _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
