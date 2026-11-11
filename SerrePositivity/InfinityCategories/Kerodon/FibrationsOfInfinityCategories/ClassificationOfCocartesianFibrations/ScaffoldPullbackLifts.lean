module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackProjections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldHorizontalDetection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OverPullbackEdges

/-!
概要：任意の部分底の辺と同じ始点・底を持つ scaffold の水平 lift。
方針：元の水平辺を指定された部分底の辺と pullback に組み合わせる。
規約：部分底とその引き戻しの quasicategory 性は不要。
使われ方：同じ scaffold 前合成の cocartesian 辺保存条件の反映。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ scaffold 比較の像には、各辺と始点・底を共有する cocartesian lift がある。 -/
lemma exists_cocartesianScaffoldPullbackMatchingLift
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (a : Over (nerve C)) (e : (pullback a.hom p) _⦋1⦌) :
    ∃ d : (pullback a.hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p))) _⦋1⦌,
      (pullback a.hom p).δ 1
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackOverMap p a).left.app (Opposite.op ⦋1⦌) d) =
          (pullback a.hom p).δ 1 e ∧
      (pullback.fst a.hom p).app (Opposite.op ⦋1⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackOverMap p a).left.app (Opposite.op ⦋1⦌) d) =
          (pullback.fst a.hom p).app (Opposite.op ⦋1⦌) e ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackOverMap p a).left.app (Opposite.op ⦋1⦌) d) := by
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p)
  let l : pullback a.hom r ⟶ pullback a.hom p :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackOverMap p a).left
  let ε := (pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_kanUniversalScaffold_horizontal_with_source p ε
  let σ := p.app (Opposite.op ⦋1⦌) ε
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) σ.hom s
  have ht : r.app (Opposite.op ⦋1⦌) t = σ := ComposableArrows.mk₁_hom σ
  let β := SSet.yonedaEquiv.symm e ≫ pullback.fst a.hom p
  have hβ : β ≫ a.hom = SSet.yonedaEquiv.symm σ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
  let d : (Δ[1] : SSet.{u}) ⟶ pullback a.hom r := pullback.lift β
    (SSet.yonedaEquiv.symm t) (by rw [SSet.yonedaEquiv_symm_comp, ht]; exact hβ)
  have hfst : d ≫ l ≫ pullback.fst a.hom p = β := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackOverMap_fst, pullback.lift_fst]
  have hsnd : d ≫ l ≫ pullback.snd a.hom p =
      SSet.yonedaEquiv.symm t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackOverMap_snd, ← Category.assoc, pullback.lift_snd]
  have hsrc : stdSimplex.δ 1 ≫ (d ≫ l) =
      stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm e := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using congrArg (fun k ↦ stdSimplex.δ 1 ≫ k) hfst
    · simp only [Category.assoc]
      rw [hsnd, ← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm,
        SSet.yonedaEquiv_symm_comp, δ_naturality_apply, hs,
        SSet.yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm]
  have him : l.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv d) =
      SSet.yonedaEquiv (d ≫ l) := (SSet.yonedaEquiv_comp d l).symm
  refine ⟨SSet.yonedaEquiv d, ?_, ?_, ?_⟩
  · change (pullback a.hom p).δ 1 (l.app _ (SSet.yonedaEquiv d)) = _
    rw [him]
    apply SSet.yonedaEquiv.symm.injective
    simpa only [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply] using hsrc
  · change (pullback.fst a.hom p).app _ (l.app _ (SSet.yonedaEquiv d)) = _
    rw [him, ← SSet.yonedaEquiv_comp (d ≫ l) (pullback.fst a.hom p), Category.assoc, hfst,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_iff p a _).mpr
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      ((pullback.snd a.hom p).app _ (l.app _ (SSet.yonedaEquiv d)))
    rw [him, ← SSet.yonedaEquiv_comp (d ≫ l) (pullback.snd a.hom p), Category.assoc, hsnd,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_horizontal p σ.hom s

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
