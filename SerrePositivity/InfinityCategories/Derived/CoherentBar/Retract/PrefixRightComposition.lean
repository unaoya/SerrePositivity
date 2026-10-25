module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BlockTransport
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.TailAtDegeneracy
/-!
概要：prefix の後の tail の退化を合成し、中間シフトの単位を消す。
方針：元の tail を始点にした退化ブロックを同じ単位へ戻し、シフト合成則を使う。
規約：元の prefix の全高次係数と、切断後の単体・次数を保持する。
使われ方：正規化境界の prefix 項を両側で同じ係数にする。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarDegeneracyBlock_prefix_before_comp {n : ℕ} (s : I _⦋n⦌)
    (k q : ℕ) (hk : k + 1 ≤ n) :
    HEq (compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarTail s (k + 1) hk)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F
        (dgCoherentBarDegeneracyAt q (dgCoherentBarTail s (k + 1) hk))))
      (dgCoherentBarDegeneracyBlock R D F (dgCoherentBarTail s (k + 1) hk).2
        ⟨n - (k + 1) - q, by change n - (k + 1) - q < n - (k + 1) + 1; omega⟩)
      (dgCoherentBarPrefixBlock R D F s k hk) (show (1 : ℤ) + -1 = 0 from rfl))
      (moduleHomShiftBlock R D (n : ℤ) (((n - (k + 1) + 1 : ℕ) : ℤ))
        (dgCoherentBarPrefixHom R D F s k hk)
        (by omega : (n : ℤ) + -(k : ℤ) - ((n - (k + 1) + 1 : ℕ) : ℤ) = 0)) := by
  let t := dgCoherentBarTail s (k + 1) hk
  let M := dgCoherentBarSource R D F ⟨n, s⟩
  let N := dgCoherentBarSource R D F t
  let i : Fin (t.1 + 1) := ⟨t.1 - q, by omega⟩
  have hN := dgCoherentBarSource_degeneracy R D F t.2 i
  have hd : HEq (dgCoherentBarDegeneracyBlock R D F t.2 i)
      (moduleHomShiftBlock R D (t.1 : ℤ) (((t.1 + 1 : ℕ) : ℤ))
        (unitElement R N).val (by omega : (t.1 : ℤ) + 0 - ((t.1 + 1 : ℕ) : ℤ) = -1)) := by
    unfold dgCoherentBarDegeneracyBlock
    exact (dgModuleHomTargetTransport R D _ _ _ _ _ _).property
  have h := gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl rfl (congrArg (shiftModule ((t.1 + 1 : ℕ) : ℤ)) hN)
    rfl rfl rfl
    (dgCoherentBarDegeneracyBlock R D F t.2 i)
    (dgCoherentBarPrefixBlock R D F s k hk)
    (moduleHomShiftBlock R D (t.1 : ℤ) ((t.1 + 1 : ℕ) : ℤ)
      (unitElement R N).val (by omega : (t.1 : ℤ) + 0 - ((t.1 + 1 : ℕ) : ℤ) = -1))
    (dgCoherentBarPrefixBlock R D F s k hk)
    hd HEq.rfl (show (1 : ℤ) + -1 = 0 from rfl) (show (1 : ℤ) + -1 = 0 from rfl)
  have hc := moduleHomShiftBlock_comp R D (n : ℤ) (t.1 : ℤ) ((t.1 + 1 : ℕ) : ℤ)
    (dgCoherentBarPrefixHom R D F s k hk) (unitElement R N).val
    (by change (n : ℤ) + -(k : ℤ) - ((n - (k + 1) : ℕ) : ℤ) = 1; omega)
    (by omega : (t.1 : ℤ) + 0 - ((t.1 + 1 : ℕ) : ℤ) = -1)
    (show (1 : ℤ) + -1 = 0 from rfl)
  have hu := unit_compose_of_heq (A := R) (D := RightModule R D)
    (unitElement R N).val (dgCoherentBarPrefixHom R D F s k hk) rfl rfl rfl HEq.rfl
  exact h.trans ((heq_of_eq hc).trans (dgBarRetractShiftBlock_heq R D M N M N
    rfl rfl _ _ _ _ rfl rfl (add_zero (-(k : ℤ))) rfl _ _ hu _ _))

end SerrePositivity.InfinityCategories
