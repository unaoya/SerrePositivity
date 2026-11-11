module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertingDescent

/-!
概要：底の宇宙持ち上げと、全単体の圏の厳密な比較。
方針：次数と単体作用素を保持し、単体の値だけを ULift する二つの関手を作る。
規約：元の底と持ち上げ先の宇宙は独立に保つ。
使われ方：宇宙を持ち上げた初頂点写像の局所化への移送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 全単体の圏の対象と射を、底を持ち上げた全単体の圏へ写す。 -/
def transportSimplexUliftUp (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory ((SSet.uliftFunctor.{v, u}).obj B) where
  obj s := ULiftHom.objUp (((SSet.uliftFunctor.{v, u}).obj B).elementsMk s.objDown.obj
    (ULift.up s.objDown.val))
  map f := ⟨{ hom := f.down.hom, map_val := congrArg ULift.up f.down.map_val }⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 持ち上げた底の全単体の圏で、単体の値の ULift だけを忘れる。 -/
def transportSimplexUliftDown (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory ((SSet.uliftFunctor.{v, u}).obj B) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B where
  obj s := ULiftHom.objUp (B.elementsMk s.objDown.obj s.objDown.val.down)
  map f := ⟨{ hom := f.down.hom, map_val := congrArg ULift.down f.down.map_val }⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の全単体の圏を持ち上げて戻す合成は、厳密に恒等関手。 -/
lemma transportSimplexUliftUp_down (B : SSet.{u}) :
    transportSimplexUliftUp.{u, v} B ⋙ transportSimplexUliftDown B = 𝟭 _ := rfl

/-- 持ち上げた全単体の圏を戻して再び持ち上げる合成も、厳密に恒等関手。 -/
lemma transportSimplexUliftDown_up (B : SSet.{u}) :
    transportSimplexUliftDown.{u, v} B ⋙ transportSimplexUliftUp B = 𝟭 _ := rfl

/-- 持ち上げる関手は、指定辺の条件を保ち反映する。 -/
lemma transportSimplexUliftUp_initialEdges (B : SSet.{u})
    (s : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) _⦋1⦌) :
    (s ⋙ transportSimplexUliftUp.{u, v} B) ∈
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges ((SSet.uliftFunctor.{v, u}).obj B) ↔
      s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges_mem_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges_mem_iff]
  rfl

/-- 宇宙の持ち上げを忘れる関手も、指定辺の条件を保ち反映する。 -/
lemma transportSimplexUliftDown_initialEdges (B : SSet.{u})
    (s : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory ((SSet.uliftFunctor.{v, u}).obj B))) _⦋1⦌) :
    (s ⋙ transportSimplexUliftDown B) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B ↔
      s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges ((SSet.uliftFunctor.{v, u}).obj B) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges_mem_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges_mem_iff]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
