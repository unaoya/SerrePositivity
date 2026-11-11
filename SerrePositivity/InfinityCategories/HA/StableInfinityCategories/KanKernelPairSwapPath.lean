module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PullbackSimplex

/-! # 自己引き戻しの交換を固定 fiber に戻す辺

概要：交換された固定 fiber の頂点を、同じ底の辺を持つ二成分の辺で固定 fiber に戻す。
方針：可縮な全空間で基点へ向かう辺を選び、その底の辺を基点から持ち上げる。
規約：辺の底への像は厳密に等しい。使われ方：交換と逆射の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：交換された代表頂点から固定 fiber の代表頂点へ、底で同じ辺となる二成分を持つ辺がある。
方針：元の頂点から基点への辺を選び、その像を基点から持ち上げて引き戻しへ組にする。
規約：E の可縮性と r の Kan fibration 性だけを使う。使われ方：ループ比較の逆射公式。 -/
lemma exists_kanKernelPairSwap_fiber_path {E B : SSet.{u}} [KanComplex E]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r (r.app (Opposite.op ⦋0⦌) e)) _⦋0⦌) :
    ∃ (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r (r.app (Opposite.op ⦋0⦌) e)) _⦋0⦌)
      (a : SSet.Truncated.Edge (X := (truncation 2).obj E) e t.val)
      (b : SSet.Truncated.Edge (X := (truncation 2).obj E) s.val e),
      r.app (Opposite.op ⦋1⦌) a.edge = r.app (Opposite.op ⦋1⦌) b.edge ∧
      SSet.mapπ₀ (pullbackSymmetry r r).hom
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion r e) (SSet.π₀.mk s)) =
      SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion r e) (SSet.π₀.mk t) := by
  obtain ⟨b⟩ := (hE.isInitialVertex s.val).nonempty_edge e
  have hs : r.app (Opposite.op ⦋0⦌) s.val = r.app (Opposite.op ⦋0⦌) e :=
    s.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
  let β : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (r.app (Opposite.op ⦋0⦌) e) (r.app (Opposite.op ⦋0⦌) e) :=
    { edge := r.app (Opposite.op ⦋1⦌) b.edge
      src_eq := (b.map ((truncation 2).map r)).src_eq.trans hs
      tgt_eq := (b.map ((truncation 2).map r)).tgt_eq }
  obtain ⟨F, hF₀, hFr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftEdge_source r e β
  let v := SSet.yonedaEquiv F
  have hv : r.app (Opposite.op ⦋1⦌) v = r.app (Opposite.op ⦋1⦌) b.edge := by
    rw [← SSet.yonedaEquiv_comp, hFr]
    exact (SSet.yonedaEquiv (X := B) (n := ⦋1⦌)).apply_symm_apply β.edge
  have hv₀ : E.δ 1 v = e := by
    have h := congrArg (SSet.yonedaEquiv (X := E) (n := ⦋0⦌)) hF₀
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using h
  have ht : r.app (Opposite.op ⦋0⦌) (E.δ 0 v) = r.app (Opposite.op ⦋0⦌) e := by
    calc
      _ = B.δ 0 (r.app (Opposite.op ⦋1⦌) v) :=
        ConcreteCategory.congr_hom (r.naturality (SimplexCategory.δ 0).op) v
      _ = _ := by rw [hv]; exact (b.map ((truncation 2).map r)).tgt_eq
  let t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r (r.app (Opposite.op ⦋0⦌) e)) _⦋0⦌ :=
    ⟨E.δ 0 v, ht.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩
  let a : SSet.Truncated.Edge (X := (truncation 2).obj E) e t.val :=
    ⟨v, hv₀, rfl⟩
  refine ⟨t, a, b, hv, ?_⟩
  let G : (Δ[1] : SSet.{u}) ⟶ pullback r r :=
    pullback.lift F (SSet.yonedaEquiv.symm b.edge) (by
      rw [hFr, SSet.yonedaEquiv_symm_comp]; rfl)
  have hG₀ : stdSimplex.δ 1 ≫ G = SSet.yonedaEquiv.symm
      ((pullbackSymmetry r r).hom.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion r e).app (Opposite.op ⦋0⦌) s)) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, G, pullback.lift_fst]
      simp only [← SSet.yonedaEquiv_symm_comp, Category.assoc,
        pullbackSymmetry_hom_comp_fst, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_snd, hF₀,
        SSet.comp_const, SSet.yonedaEquiv_symm_zero]
    · simp only [Category.assoc, G, pullback.lift_snd]
      simp only [← SSet.yonedaEquiv_symm_comp, Category.assoc,
        pullbackSymmetry_hom_comp_snd, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_fst, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source]
      rw [SSet.yonedaEquiv_symm_comp]
      rfl
  have hG₁ : stdSimplex.δ 0 ≫ G = SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion r e).app (Opposite.op ⦋0⦌) t) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, G, pullback.lift_fst]
      simp only [← SSet.yonedaEquiv_symm_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_fst]
      rw [SSet.yonedaEquiv_symm_comp]
      have ha : SSet.yonedaEquiv.symm a.edge = F :=
        (SSet.yonedaEquiv (X := E) (n := ⦋1⦌)).symm_apply_apply F
      rw [← ha]
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target a
    · simp only [Category.assoc, G, pullback.lift_snd]
      simp only [← SSet.yonedaEquiv_symm_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_snd,
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target, SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  let g : SSet.Truncated.Edge (X := (truncation 2).obj (pullback r r))
      ((pullbackSymmetry r r).hom.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion r e).app (Opposite.op ⦋0⦌) s))
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion r e).app (Opposite.op ⦋0⦌) t) :=
    { edge := SSet.yonedaEquiv G
      src_eq := by
        have h := congrArg (SSet.yonedaEquiv (X := pullback r r) (n := ⦋0⦌)) hG₀
        simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using! h
      tgt_eq := by
        have h := congrArg (SSet.yonedaEquiv (X := pullback r r) (n := ⦋0⦌)) hG₁
        simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using! h }
  exact SSet.π₀.sound (SSet.Edge.ofTruncated g)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
