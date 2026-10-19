module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberPullback
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberExists

/-! # dg 加群の nerve の全ての辺の fiber

概要：shifted cone の実普遍性を任意の辺の fiber の存在へ昇格する。
方針：閉加群射と辺の同値を使い、入力辺を厳密に保つ引き戻し四角形を作る。
規約：h の fiber で代用しない。使われ方：β3 の dg 加群模型の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉 dg 加群射の shifted cone は実際の辺の fiber を与える。 -/
def dgModuleFiberSquareOfMorphism {M N : ModuleCategory A D} (f : M ⟶ N) :
    FiberSquare (X := dgModuleNerve A D) (dgModuleEdge A D f).toTruncated where
  toZeroTriangle := dgModuleFiberZeroTriangle A D f
  right_edge := dgModuleFiberSquare_right A D f
  isPullback := dgModuleFiberSquare_isPullback A D f

/-- 全 Hom end を持つ dg 加群圏の nerve の全ての辺は実 fiber を持つ。 -/
lemma dgModuleNerve_fiber_exists {x y : (dgModuleNerve A D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D)) x y) :
    Nonempty (FiberSquare e) := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  change Nonempty (FiberSquare (X := dgModuleNerve A D)
    (e : SSet.Truncated.Edge (Simplex.vertex M) (Simplex.vertex N)))
  rw [← dgModuleEdge_edgeClosed A D e]
  exact ⟨dgModuleFiberSquareOfMorphism A D (edgeClosed e)⟩

end SerrePositivity.InfinityCategories
