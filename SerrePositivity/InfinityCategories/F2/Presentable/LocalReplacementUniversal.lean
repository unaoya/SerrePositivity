module

public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeTargetCocone
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeFamily

/-!
概要：局所対象へ向かう元の局所同値は、局所対象への普遍矢印。
方針：終点を重ねる元の退化三角形で、二つの局所余錐制限の始対象性を移す。
規約：元の辺を選んだ同型な代表へ置き換えない。
使われ方：HTT 5.5.4.15 の局所置換から反射の存在への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X : SSet.{u}} [Quasicategory X]

private lemma localRestriction_vertex_fst (W : Set (X _⦋1⦌))
    {J K : SSet.{u}} (D : J ⟶ X) (d : K ⟶ X) (i : K ⟶ J) (hi : i ≫ D = d)
    (c : JoinCocone D) (hc : IsLocalObject W c.vertex) :
    (pullback.fst (sliceUnderProjection d) (localObjectsSubcomplex W).ι).app
      (Opposite.op ⦋0⦌) ((localTargetCoconeRestriction W D d i hi).app
        (Opposite.op ⦋0⦌) (localTargetCoconeVertex W c hc)) =
      (normalizedCoconeRestriction D i hi).app (Opposite.op ⦋0⦌) c := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (localTargetCoconeVertex W c hc))
    (localTargetCoconeRestriction_fst W D d i hi)
  simp only [NatTrans.comp_app_apply] at h
  dsimp only [localTargetCoconeSpace] at h ⊢
  exact h.trans (congrArg ((normalizedCoconeRestriction D i hi).app (Opposite.op ⦋0⦌))
    (localTargetCoconeVertex_fst W c hc))

/-- 元の局所同値の終点が局所なら、その辺は局所対象への余錐圏で始対象。 -/
lemma localReplacement_edgeSource_isInitial (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv e ∈ localEquivalences W)
    (hy : IsLocalObject W (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))) :
    IsInitialVertex (localTargetCoconeVertex W (edgeSourcePointCocone e)
      (by rw [edgeSourcePointCocone_vertex]; exact hy)) := by
  let c := localTargetCoconeVertex W (edgeTargetCocone e)
    (by rw [edgeTargetCocone_vertex]; exact hy)
  let r₀ := localTargetCoconeRestriction W e (stdSimplex.δ (0 : Fin 2) ≫ e)
    (stdSimplex.δ (0 : Fin 2)) rfl
  let r₁ := localTargetCoconeRestriction W e (stdSimplex.δ (1 : Fin 2) ≫ e)
    (stdSimplex.δ (1 : Fin 2)) rfl
  have h₀ := localTargetCoconeRestriction_target_isQCatEquivalence W e
  have h₁ := localTargetCoconeRestriction_source_isQCatEquivalence W e he
  have ht : IsInitialVertex (r₀.app (Opposite.op ⦋0⦌) c) := by
    apply localTargetCocone_isInitial_of_ambient
    rw [localRestriction_vertex_fst]
    exact edgeTargetCocone_target_isColimit e
  have hc : IsInitialVertex c := (h₀.choose.isInitialVertex_iff c).mpr ht
  have hs : IsInitialVertex (r₁.app (Opposite.op ⦋0⦌) c) := h₁.choose.map_isInitialVertex hc
  have heq := localTargetCoconeVertex_eq_of_fst W (r₁.app (Opposite.op ⦋0⦌) c)
    (edgeSourcePointCocone e) (by rw [edgeSourcePointCocone_vertex]; exact hy) (by
      rw [localRestriction_vertex_fst]
      exact edgeTargetCocone_source e)
  exact heq ▸ hs

end SerrePositivity.InfinityCategories.HomotopyLimits
