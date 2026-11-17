module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicFactorWidth
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstFaceWidth
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionLastFaceAtomicity
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthFaces

/-!
概要：非原子的な実境界面の原子分解に現れる任意の因子は、元の実鎖より幅が小さい。
方針：境界面の実非原子性と全実面の幅の非増加を、実道の任意の因子の厳密な境界と合わせる。
規約：先頭因子だけでなく任意の位置の実因子を扱う。
使われ方：Riehl–Verity Proposition 4.2.15の境界面の全原子分解、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの順序づけ。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：非退化な実原子の最後の実面の任意の実原子因子は、元の実鎖より幅が小さい。
方針：面の実非原子性と道の指定因子の幅の厳密な境界を、全実面の非増加へ合成する。
規約：元の全実関手との等式で実因子分解を指定。使われ方：Riehl–Verity §4.2の最後の実面。 -/
lemma walkingAdjunctionLastFace_atomicFactor_width_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1))
    {B C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨X⟩⟩ : WalkingAdjunctionAtomicVertex n) B) (e : B ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 1))) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth H := by
  have h := walkingAdjunctionAtomicFactor_width_lt q e r (by
    rw [hfac]
    exact walkingAdjunctionLastFace_not_atomic H ha hnd)
  rw [hfac] at h
  exact lt_of_lt_of_le h (walkingAdjunctionOrdinalWidth_face_le n H (Fin.last (n + 1)))

/-- 概要：最初の併合より前の先頭の実面の任意の実原子因子は、元の実鎖より幅が小さい。
方針：先頭面の実非原子性と幅の保存を、道の指定実因子の幅の厳密な境界に適用する。
規約：実最小元が先頭でない場合。使われ方：Riehl–Verity §4.2の先頭の実面の全因子。 -/
lemma walkingAdjunctionFirstFace_atomicFactor_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {B C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) B) (e : B ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = H.δ₀) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth H := by
  have hf := walkingAdjunctionFirstFace_width_and_not_atomic H ha hnd hk
  have h := walkingAdjunctionAtomicFactor_width_lt q e r (by rw [hfac]; exact hf.2)
  rw [hfac, hf.1] at h
  exact h

end SerrePositivity.InfinityCategories.HA.Monads
