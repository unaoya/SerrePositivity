module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalCoconeInitial

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.EdgeTargetCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamily

/-!
概要：局所対象へ向かう元の局所同値は、局所対象への普遍矢印。
方針：終点を重ねる元の退化三角形で、二つの局所余錐制限の始対象性を移す。
規約：元の辺を選んだ同型な代表へ置き換えない。
使われ方：HTT 5.5.4.15 の局所置換から反射の存在への接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {X : SSet.{u}} [Quasicategory X]

private lemma localRestriction_vertex_fst (W : Set (X _⦋1⦌))
    {J K : SSet.{u}} (D : J ⟶ X) (d : K ⟶ X) (i : K ⟶ J) (hi : i ≫ D = d)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W c.vertex) :
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection d) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W).ι).app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeRestriction W D d i hi).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeVertex W c hc)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction D i hi).app (Opposite.op ⦋0⦌) c := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeVertex W c hc))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeRestriction_fst W D d i hi)
  simp only [NatTrans.comp_app_apply] at h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeSpace] at h ⊢
  exact h.trans (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction D i hi).app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeVertex_fst W c hc))

/-- 元の局所同値の終点が局所なら、その辺は局所対象への余錐圏で始対象。 -/
lemma localReplacement_edgeSource_isInitial (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv e ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeVertex W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeSourcePointCocone e)
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeSourcePointCocone_vertex]; exact hy)) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeVertex W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone e)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone_vertex]; exact hy)
  let r₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeRestriction W e (stdSimplex.δ (0 : Fin 2) ≫ e)
    (stdSimplex.δ (0 : Fin 2)) rfl
  let r₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeRestriction W e (stdSimplex.δ (1 : Fin 2) ≫ e)
    (stdSimplex.δ (1 : Fin 2)) rfl
  have h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeRestriction_target_isQCatEquivalence W e
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeRestriction_source_isQCatEquivalence W e he
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (r₀.app (Opposite.op ⦋0⦌) c) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCocone_isInitial_of_ambient
    rw [localRestriction_vertex_fst]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone_target_isColimit e
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c := (h₀.choose.isInitialVertex_iff c).mpr ht
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (r₁.app (Opposite.op ⦋0⦌) c) := h₁.choose.map_isInitialVertex hc
  have heq := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeVertex_eq_of_fst W (r₁.app (Opposite.op ⦋0⦌) c)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeSourcePointCocone e) (by rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeSourcePointCocone_vertex]; exact hy) (by
      rw [localRestriction_vertex_fst]
      exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone_source e)
  exact heq ▸ hs

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
