module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldPullbackProjections
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldHorizontalDetection
public import SerrePositivity.InfinityCategories.F1.CocartesianOverPullbackEdges

/-!
概要：任意の部分底の辺と同じ始点・底を持つ scaffold の水平 lift。
方針：元の水平辺を指定された部分底の辺と pullback に組み合わせる。
規約：部分底とその引き戻しの quasicategory 性は不要。
使われ方：同じ scaffold 前合成の cocartesian 辺保存条件の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ scaffold 比較の像には、各辺と始点・底を共有する cocartesian lift がある。 -/
lemma exists_cocartesianScaffoldPullbackMatchingLift
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C)
    [CocartesianFibration p] (a : Over (nerve C)) (e : (pullback a.hom p) _⦋1⦌) :
    ∃ d : (pullback a.hom
        (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))) _⦋1⦌,
      (pullback a.hom p).δ 1
        ((cocartesianScaffoldPullbackOverMap p a).left.app (Opposite.op ⦋1⦌) d) =
          (pullback a.hom p).δ 1 e ∧
      (pullback.fst a.hom p).app (Opposite.op ⦋1⦌)
        ((cocartesianScaffoldPullbackOverMap p a).left.app (Opposite.op ⦋1⦌) d) =
          (pullback.fst a.hom p).app (Opposite.op ⦋1⦌) e ∧
      IsCocartesianEdge (pullback.fst a.hom p)
        ((cocartesianScaffoldPullbackOverMap p a).left.app (Opposite.op ⦋1⦌) d) := by
  let r := simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)
  let l : pullback a.hom r ⟶ pullback a.hom p :=
    (cocartesianScaffoldPullbackOverMap p a).left
  let ε := (pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e
  obtain ⟨s, hs⟩ := exists_kanUniversalScaffold_horizontal_with_source p ε
  let σ := p.app (Opposite.op ⦋1⦌) ε
  let t := kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p) σ.hom s
  have ht : r.app (Opposite.op ⦋1⦌) t = σ := ComposableArrows.mk₁_hom σ
  let β := SSet.yonedaEquiv.symm e ≫ pullback.fst a.hom p
  have hβ : β ≫ a.hom = SSet.yonedaEquiv.symm σ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
  let d : (Δ[1] : SSet.{u}) ⟶ pullback a.hom r := pullback.lift β
    (SSet.yonedaEquiv.symm t) (by rw [SSet.yonedaEquiv_symm_comp, ht]; exact hβ)
  have hfst : d ≫ l ≫ pullback.fst a.hom p = β := by
    rw [cocartesianScaffoldPullbackOverMap_fst, pullback.lift_fst]
  have hsnd : d ≫ l ≫ pullback.snd a.hom p =
      SSet.yonedaEquiv.symm t ≫ kanUniversalScaffold p := by
    rw [cocartesianScaffoldPullbackOverMap_snd, ← Category.assoc, pullback.lift_snd]
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
  · apply (isCocartesianEdge_overPullback_iff p a _).mpr
    change IsCocartesianEdge p
      ((pullback.snd a.hom p).app _ (l.app _ (SSet.yonedaEquiv d)))
    rw [him, ← SSet.yonedaEquiv_comp (d ≫ l) (pullback.snd a.hom p), Category.assoc, hsnd,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact kanUniversalScaffold_horizontal p σ.hom s

end SerrePositivity.InfinityCategories
