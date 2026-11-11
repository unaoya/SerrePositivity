module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PullbackTerminalVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools

/-!
概要：任意の厳密な引き戻し正方形での成分ごとの終対象性。
方針：元の頂点を標準引き戻しへ同型で移し、写像空間の判定を使う。
規約：元の正方形の射影と頂点を保持する。
使われ方：錐族の引き戻し正方形から極限錐を判定する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：inner fibration を一脚とする引き戻しの三成分が終対象なら元の頂点も終対象。
方針：標準引き戻しとの同型で三成分を照合し、写像空間の可縮性を使う。
規約：元の頂点 x の終対象性を結論する。
使われ方：引き戻し内の図式の成分ごとの極限錐判定。 -/
lemma isTerminalVertex_of_isPullback_of_components {W E D B : SSet.{u}}
    [Quasicategory W] [Quasicategory E] [Quasicategory D] [Quasicategory B]
    {a : W ⟶ E} {b : W ⟶ D} {p : E ⟶ B} {q : D ⟶ B}
    (s : IsPullback a b p q) [InnerFibration p] (x : W _⦋0⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (a.app (Opposite.op ⦋0⦌) x))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (b.app (Opposite.op ⦋0⦌) x))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((a ≫ p).app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso s.isoPullback).isTerminalVertex_iff x).2
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isTerminalVertex_pullback_of_components p q (fun _ _ ↦ inferInstance)
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
      ((s.isoPullback.hom ≫ pullback.fst p q).app (Opposite.op ⦋0⦌) x)
    rw [s.isoPullback_hom_fst]
    exact he
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
      ((s.isoPullback.hom ≫ pullback.snd p q).app (Opposite.op ⦋0⦌) x)
    rw [s.isoPullback_hom_snd]
    exact hd
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
      (((s.isoPullback.hom ≫ pullback.fst p q) ≫ p).app (Opposite.op ⦋0⦌) x)
    rw [s.isoPullback_hom_fst]
    exact hb

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
