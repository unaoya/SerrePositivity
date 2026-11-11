module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeFunctor
public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso

/-!
# 元の全複体から実自由 probe を通る CAlg_R 値関手

概要：元の複体 nerve の全単体を同じ自由 probe の CAlg_R 像へ送る。
方針：同じ実自由 probe 関手と既存の全代数局所化源を合成する。
規約：全複体の擬同型を反転し、元の自由代数頂点との比較を保持する。
使われ方：同じ U の左導来随伴を既存 D(R) から構成するための局所化入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

def freeProbeCAlgSource : nerve (Complex A) ⟶ CAlg_R A :=
  nerveMap (freeProbeFunctor A) ≫ algebraCAlgSource A

lemma freeProbeCAlgSource_map_weak {X Y : Complex A} (f : X ⟶ Y) (hf : QuasiIso f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map (freeProbeCAlgSource A)).toTruncated := by
  have h := algebraCAlgSource_map_weak A ((freeProbeFunctor A).map f)
    (freeProbeFunctor_map_quasiIso A f hf)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := ((nerve.edgeMk ((freeProbeFunctor A).map f)).map (algebraCAlgSource A)).toTruncated)
    (f := ((nerve.edgeMk f).map (freeProbeCAlgSource A)).toTruncated) ?_).mp h
  change (algebraCAlgSource A).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ ((freeProbeFunctor A).map f)) =
      (freeProbeCAlgSource A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)
  simp only [freeProbeCAlgSource, NatTrans.comp_app_apply, nerveMap_app_mk₁]

def freeProbeCAlgSource_vertexIso (X : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((freeProbeCAlgSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      (cAlgVertex A ((freeProbeFunctor A).obj X)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
    ((nerveMap (freeProbeFunctor A)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))) _
  rw [nerveMap_app_mk₀]
  exact algebraCAlgSource_vertexIso A _

end SerrePositivity.EInfinity.BarrattEccles
