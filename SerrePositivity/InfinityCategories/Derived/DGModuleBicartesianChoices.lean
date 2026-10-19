module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberExists
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberPushout
public import SerrePositivity.InfinityCategories.Derived.DGModuleConePullback

/-! # dg 加群 nerve の全辺の双カルテジアンな選択

概要：任意の実際の辺に、その辺を厳密に保つ双カルテジアンな fiber/cofiber を与える。
方針：閉 dg 加群射の標準四角形を辺の復元等式で輸送する。
規約：安定性を仮定しない。使われ方：dgModuleNerve の安定性の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Hom end の dg 加群 nerve の全ての辺に双カルテジアンな cofiber がある。 -/
lemma dgModuleNerve_bicartesian_cofiber_exists {x y : (dgModuleNerve A D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D)) x y) :
    ∃ s : CofiberSquare e, IsPullbackSquare s.square := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  change ∃ s : CofiberSquare (X := dgModuleNerve A D)
    (e : SSet.Truncated.Edge (Simplex.vertex M) (Simplex.vertex N)), IsPullbackSquare s.square
  rw [← dgModuleEdge_edgeClosed A D e]
  exact ⟨dgModuleCofiberSquare A D (edgeClosed e), dgModuleConeSquare_isPullback A D _⟩

/-- 全 Hom end の dg 加群 nerve の全ての辺に双カルテジアンな fiber がある。 -/
lemma dgModuleNerve_bicartesian_fiber_exists {x y : (dgModuleNerve A D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D)) x y) :
    ∃ s : FiberSquare e, IsPushoutSquare s.square := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  change ∃ s : FiberSquare (X := dgModuleNerve A D)
    (e : SSet.Truncated.Edge (Simplex.vertex M) (Simplex.vertex N)), IsPushoutSquare s.square
  rw [← dgModuleEdge_edgeClosed A D e]
  exact ⟨dgModuleFiberSquareOfMorphism A D (edgeClosed e), dgModuleFiberSquare_isPushout A D _⟩

end SerrePositivity.InfinityCategories
