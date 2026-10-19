module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConePushout

/-! # dg 加群の nerve の全ての辺の cofiber

概要：実 cone の普遍性を任意の辺の cofiber の存在へ昇格する。
方針：全 Hom end の閉射と辺の同値を使い、入力辺を厳密に保つ四角形を作る。
規約：二切断の辺の代表を選び直して済ませない。使われ方：β3 の dg 加群模型の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉 dg 加群射の標準 cone はその実際の辺の cofiber を与える。 -/
def dgModuleCofiberSquare {M N : ModuleCategory A D} (f : M ⟶ N) :
    CofiberSquare (X := dgModuleNerve A D) (dgModuleEdge A D f).toTruncated where
  toZeroTriangle := dgModuleConeZeroTriangle A D f
  bottom_edge := dgModuleConeSquare_bottom A D f
  isPushout := dgModuleConeSquare_isPushout A D f

/-- dg 加群 nerve の辺は閉 dg 加群射の実際の辺として復元できる。 -/
lemma dgModuleEdge_edgeClosed {M N : RightModule A D}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D))
      (Simplex.vertex M) (Simplex.vertex N)) :
    (dgModuleEdge A D (edgeClosed e)).toTruncated = e :=
  (edgeClosedEquiv (Simplex.vertex M) (Simplex.vertex N)).symm_apply_apply e

/-- 全 Hom end を持つ dg 加群圏の nerve の全ての辺は実 cofiber を持つ。 -/
lemma dgModuleNerve_cofiber_exists {x y : (dgModuleNerve A D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D)) x y) :
    Nonempty (CofiberSquare e) := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  change Nonempty (CofiberSquare (X := dgModuleNerve A D)
    (e : SSet.Truncated.Edge (Simplex.vertex M) (Simplex.vertex N)))
  rw [← dgModuleEdge_edgeClosed A D e]
  exact ⟨dgModuleCofiberSquare A D (edgeClosed e)⟩

end SerrePositivity.InfinityCategories
