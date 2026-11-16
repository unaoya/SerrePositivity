module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBoundaryFactorWidth
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthRefinement

/-!
概要：非原子的な実境界面のminus始点の非退化原子因子では、実細分の幅も元より小さい。
方針：全実原子因子の幅の境界を、構成済みの実最初の細分の幅の保存へ移す。
規約：実最小元から構成した親の全関手を結論に保持する。
使われ方：Riehl–Verity Proposition 4.2.15の境界因子の実親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの実幅の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最後の実面のminus始点の非退化原子因子では、その実細分の幅も元より小さい。
方針：実細分での幅の保存と、実境界面の全原子因子の厳密な境界を合わせる。
規約：全位置の実因子。使われ方：Riehl–Verity §4.2の最後の実境界面の実親。 -/
lemma walkingAdjunctionLastFace_minusFactor_parent_width_lt {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2))
    {C : WalkingAdjunctionAtomicVertex (n + 1)}
    (q : Quiver.Path (⟨⟨X⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟨⟨.minus⟩⟩)
    (e : (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)))
    (hfac : (walkingAdjunctionAtomicPathFunctor (n + 1)).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 2)))
    (he : ULift.up e.val ∈
      (WalkingAdjunctionHomShape.{u} .minus C.level.point).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement e.val e.property he) <
      walkingAdjunctionOrdinalWidth H := by
  rw [walkingAdjunctionFirstRefinement_ordinalWidth]
  exact walkingAdjunctionLastFace_atomicFactor_width_lt H ha hnd q e r hfac

/-- 概要：最初の併合より前の先頭面のminus始点の非退化原子因子の実細分は、幅が元より小さい。
方針：先頭面の非原子性による実因子の厳密な境界を、実細分の幅の保存へ移す。
規約：全位置の実因子。使われ方：Riehl–Verity §4.2の先頭の実境界面の実親。 -/
lemma walkingAdjunctionFirstFace_minusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {C : WalkingAdjunctionAtomicVertex (n + 1)}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟨⟨.minus⟩⟩)
    (e : (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)))
    (hfac : (walkingAdjunctionAtomicPathFunctor (n + 1)).map (q.comp (e.toPath.comp r)) = H.δ₀)
    (he : ULift.up e.val ∈
      (WalkingAdjunctionHomShape.{u} .minus C.level.point).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement e.val e.property he) <
      walkingAdjunctionOrdinalWidth H := by
  rw [walkingAdjunctionFirstRefinement_ordinalWidth]
  exact walkingAdjunctionFirstFace_atomicFactor_width_lt H ha hnd hk q e r hfac

end SerrePositivity.InfinityCategories.HA.Monads
