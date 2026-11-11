module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeCartesianTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily

/-! # 余錐の制限の反転による輸送

概要：余錐の制限射を反転すると cocartesian fibration になる。
方針：終点指定の cartesian lift を反転し、外側ホーン充填を双対化する。
規約：形状は任意、値域は quasicategory。
使われ方：普遍余錐の相対始点境界充填。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐の制限の反転は cocartesian fibration。
方針：基底の辺を逆向きに読み、cartesian な余錐の持ち上げを反転する。
規約：値域 X の quasicategory 性以外に形状 K の仮定は不要。
使われ方：余極限と相対始対象の同値判定。 -/
instance cocartesianHornFibration_coconeRestriction_op (K X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X)) where
  toInnerFibration := inferInstance
  exists_lift v b a := by
    let B := (ihom K).obj X
    let E := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X
    let a' : SSet.Truncated.Edge (X := (truncation 2).obj B)
        (SSet.opObjEquiv b)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X).app (Opposite.op ⦋0⦌) (SSet.opObjEquiv v)) :=
      { edge := SSet.opObjEquiv a.edge
        src_eq := by
          have h := a.tgt_eq
          change B.op.δ 0 a.edge = b at h
          rw [SSet.op_δ] at h
          exact congrArg SSet.opObjEquiv h
        tgt_eq := by
          have h := a.src_eq
          change B.op.δ 1 a.edge = _ at h
          rw [SSet.op_δ] at h
          exact congrArg SSet.opObjEquiv h }
    obtain ⟨w, e, hp, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cartesian_cocone_lift K X (SSet.opObjEquiv v)
      (SSet.opObjEquiv b) a'
    let e' : SSet.Truncated.Edge (X := (truncation 2).obj E.op) v
        (SSet.opObjEquiv.symm w) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e
    refine ⟨SSet.opObjEquiv.symm w, e', ?_, ?_⟩
    · exact congrArg SSet.opObjEquiv.symm hp
    · intro n σ β hσ hw
      have hs : CommSq σ (horn (n + 2) 0).ι
          (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X)) β := ⟨hw⟩
      have := he.op n σ β hσ hs
      exact ⟨hs.lift, hs.fac_left, hs.fac_right⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
