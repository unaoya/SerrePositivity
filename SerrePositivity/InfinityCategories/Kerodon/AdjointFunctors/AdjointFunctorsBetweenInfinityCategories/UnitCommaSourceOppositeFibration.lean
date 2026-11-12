module
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite

/-! # comma の始域射影の反転による輸送

概要：comma の始域射影を反転すると cocartesian fibration になる。
方針：終点指定の cartesian lift を反転し、外側ホーン充填を双対化する。
規約：二つの圏は quasicategory、G の fibration 性は不要。
使われ方：単位切断の相対始点境界充填。

対応節は Kerodon 6.2（Tag 02EH）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：comma の始域射影の反転は cocartesian fibration。
方針：基底の辺を逆向きに読み、cartesian な comma の持ち上げを反転する。
規約：X と Y は quasicategory。straightening は使わない。
使われ方：単位切断の fiber の始対象性を相対境界充填へ移す。 -/
instance cocartesianHornFibration_unitCommaSource_op {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G)) where
  toInnerFibration := inferInstance
  exists_lift v b a := by
    let B := X
    let E := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G
    let a' : SSet.Truncated.Edge (X := (truncation 2).obj B)
        (SSet.opObjEquiv b)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G).app (Opposite.op ⦋0⦌) (SSet.opObjEquiv v)) :=
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
    obtain ⟨w, e, hp, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_cartesian_unitComma_lift G (SSet.opObjEquiv v)
      (SSet.opObjEquiv b) a'
    let e' : SSet.Truncated.Edge (X := (truncation 2).obj E.op) v
        (SSet.opObjEquiv.symm w) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e
    refine ⟨SSet.opObjEquiv.symm w, e', ?_, ?_⟩
    · exact congrArg SSet.opObjEquiv.symm hp
    · intro n σ β hσ hw
      have hs : CommSq σ (horn (n + 2) 0).ι
          (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G)) β := ⟨hw⟩
      have := he.op n σ β hσ hs
      exact ⟨hs.lift, hs.fac_left, hs.fac_right⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
