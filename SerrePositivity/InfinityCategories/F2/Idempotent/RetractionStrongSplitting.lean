module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakEndpoints
public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakExtension

/-!
概要：指定した二頂点の元の retract を、同じ両頂点を持つ全 coherent 分裂へ戻す。
方針：元の分裂三角形を弱い全図式へ降ろし、元の inner anodyne 比較で延長する。
規約：元の分裂点と非分裂点の等式を保持する。単なる同型類で代用しない。
使われ方：辺全体の retract に対応する元の coherent 冪等図式の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の同じ二頂点の retract は、元の両頂点を厳密に持つ全 coherent 分裂となる。 -/
lemma VertexRetraction.strongSplitting_exists {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction x y) :
    ∃ (d : CoherentIdempotent X) (s : StrongSplitting d), s.vertex = x ∧ d.vertex = y := by
  obtain ⟨t, _hi, _hr⟩ := r.triangle_exists
  obtain ⟨d, s, hs⟩ := weakDiagram_strongSplitting_exists t.weakDiagram
  have himg : weakImagePoint ≫ s.weakDiagram = SSet.yonedaEquiv.symm x := by
    rw [hs]
    exact t.weakDiagram_imagePoint
  have hsrc : weakSourcePoint ≫ s.weakDiagram = SSet.yonedaEquiv.symm y := by
    rw [hs]
    exact t.weakDiagram_sourcePoint
  rw [StrongSplitting.weakDiagram, ← Category.assoc, weakComparison_imagePoint] at himg
  rw [StrongSplitting.weakDiagram, ← Category.assoc, weakComparison_sourcePoint] at hsrc
  have hx : s.vertex = x := by
    change s.val.app (Opposite.op ⦋0⦌) (nerveEquiv.symm walkingImage) = x
    have h := congrArg SSet.yonedaEquiv himg
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  have hy : s.val.app (Opposite.op ⦋0⦌) (nerveEquiv.symm walkingSource) = y := by
    have h := congrArg SSet.yonedaEquiv hsrc
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  exact ⟨d, s, hx, s.source_eq.symm.trans hy⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
