module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：元の pullback の射影の固定 fiber は、元の対応する fiber と同型。
方針：同じ二射影と固定条件を pullback の普遍性に渡す。
規約：全パラメーターで第一射影を保持する。
使われ方：実際の第二三角形の外ホーン延長の fiber 表示。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

variable {P E F B : SSet.{u}} {i : P ⟶ E} {j : P ⟶ F} {p : E ⟶ B} {q : F ⟶ B}

/-- 同じ pullback の第二射影の fiber は、対応する元の fiber と厳密に同型。 -/
def vertexFiberIsoOfIsPullback (hp : IsPullback i j p q) (b : F _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber j b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (q.app (Opposite.op ⦋0⦌) b) := by
  let ι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι j b
  let ι' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (q.app (Opposite.op ⦋0⦌) b)
  have hh : (ι ≫ i) ≫ p = SSet.const (q.app (Opposite.op ⦋0⦌) b) := by
    rw [Category.assoc, hp.w, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p (q.app (Opposite.op ⦋0⦌) b) (ι ≫ i) hh
  let L := hp.lift ι' (SSet.const b) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp])
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift j b L (hp.lift_snd _ _ _)
  have hH : H ≫ ι' = ι ≫ i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hV : V ≫ ι = L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  refine ⟨H, V, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext j b
    change (H ≫ V) ≫ ι = (𝟙 _) ≫ ι
    rw [Category.assoc, hV, Category.id_comp]
    apply hp.hom_ext
    · rw [Category.assoc, hp.lift_fst, hH]
    · rw [Category.assoc, hp.lift_snd, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p (q.app (Opposite.op ⦋0⦌) b)
    change (V ≫ H) ≫ ι' = (𝟙 _) ≫ ι'
    rw [Category.assoc, hH, ← Category.assoc, hV, Category.id_comp]
    exact hp.lift_fst _ _ _

/-- 同じ fiber 同型は、元の第一射影と全パラメーターで可換。 -/
lemma vertexFiberIsoOfIsPullback_hom_ι (hp : IsPullback i j p q) (b : F _⦋0⦌) :
    (vertexFiberIsoOfIsPullback hp b).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (q.app (Opposite.op ⦋0⦌) b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι j b ≫ i := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
