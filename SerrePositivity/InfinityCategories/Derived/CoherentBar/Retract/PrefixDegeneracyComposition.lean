module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixDegeneracyNaturality
public import SerrePositivity.DifferentialGraded.Module.ShiftBlockComposition
/-!
概要：重複頂点より前の prefix と退化ブロックの合成を、元の高次係数へ戻す。
方針：始域・終域の等式を明示し、シフト合成則で中間の退化単位を消す。
規約：全高次係数と端点輸送を保持する。自然性を次数零の辺だけに制限しない。
使われ方：正規化境界の prefix 有限和の項ごとの相殺。
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

lemma dgCoherentBarSource_tail_degeneracy_before {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k + 1 ≤ j.val) :
    dgCoherentBarSource R D F (dgCoherentBarTail (I.σ j s) (k + 1) (by omega)) =
      dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) (by omega)) := by
  have hp := congrArg (fun f => I.map f.op s)
    (dgCoherentBarPrefixOrder_degeneracy_before j (k + 1) hk)
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at hp
  have hv := congrArg (fun t : I _⦋k + 1⦌ => coherentDiagramVertex F
    (I.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ (Fin.last (k + 1))).op t)) hp
  have h₁ := dgCoherentBarPrefix_target R D F (I.σ j s) k (by omega)
  have h₂ := dgCoherentBarPrefix_target R D F s k (by omega)
  exact h₁.symm.trans (hv.trans h₂)

private lemma block_transport_heq (a b : ℤ)
    (M N M' N' : RightModule R D) (hM : M = M') (hN : N = N')
    {q p : ℤ} (f : GradedHom R M N q) (f' : GradedHom R M' N' q)
    (hf : HEq f f') (hp : a + q - b = p) :
    HEq (moduleHomShiftBlock R D a b f hp)
      (moduleHomShiftBlock R D a b f' hp) := by
  cases hM
  cases hN
  cases eq_of_heq hf
  rfl

private lemma block_degree_heq (a b : ℤ) (M N : RightModule R D)
    {q q' p p' : ℤ} (hq : q = q') (hp : p = p')
    (f : GradedHom R M N q) (f' : GradedHom R M N q') (hf : HEq f f')
    (ha : a + q - b = p) (hb : a + q' - b = p') :
    HEq (moduleHomShiftBlock R D a b f ha) (moduleHomShiftBlock R D a b f' hb) := by
  cases hq
  cases hp
  cases eq_of_heq hf
  rfl

lemma dgCoherentBarPrefixBlock_degeneracy_before_comp {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k + 1 ≤ j.val) :
    HEq (compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s j)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F
        (dgCoherentBarTail (I.σ j s) (k + 1) (by omega))))
      (dgCoherentBarPrefixBlock R D F (I.σ j s) k (by omega))
      (dgCoherentBarDegeneracyBlock R D F s j) (show (-1 : ℤ) + 1 = 0 from rfl))
      (moduleHomShiftBlock R D (n : ℤ) ((n + 1 - (k + 1) : ℕ) : ℤ)
        (dgCoherentBarPrefixHom R D F s k (by omega))
        (by omega : (n : ℤ) + -(k : ℤ) - ((n + 1 - (k + 1) : ℕ) : ℤ) = 0)) := by
  let M := dgCoherentBarSource R D F ⟨n, s⟩
  let N := dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) (by omega))
  have hm := dgCoherentBarSource_degeneracy R D F s j
  have hn := dgCoherentBarSource_tail_degeneracy_before R D F s j k hk
  have hb : HEq (dgCoherentBarPrefixBlock R D F (I.σ j s) k (by omega))
      (moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ)
        ((n + 1 - (k + 1) : ℕ) : ℤ)
        (dgCoherentBarPrefixHom R D F s k (by omega))
        (by omega : ((n + 1 : ℕ) : ℤ) + -(k : ℤ) -
          ((n + 1 - (k + 1) : ℕ) : ℤ) = 1)) := by
    unfold dgCoherentBarPrefixBlock
    exact block_transport_heq R D _ _ _ _ _ _ hm hn _ _
      (dgCoherentBarPrefixHom_degeneracy_before R D F s j k hk) _
  have hd : HEq (dgCoherentBarDegeneracyBlock R D F s j)
      (moduleHomShiftBlock R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
        (unitElement R M).val (by omega : (n : ℤ) + 0 - ((n + 1 : ℕ) : ℤ) = -1)) := by
    unfold dgCoherentBarDegeneracyBlock
    exact (dgModuleHomTargetTransport R D _ _ _ _ _ _).property
  have hh := gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl (congrArg (shiftModule ((n + 1 : ℕ) : ℤ)) hm)
    (congrArg (shiftModule ((n + 1 - (k + 1) : ℕ) : ℤ)) hn)
    rfl rfl rfl _ _ _ _ hb hd rfl rfl
  have hc := moduleHomShiftBlock_comp R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
    ((n + 1 - (k + 1) : ℕ) : ℤ)
    (unitElement R M).val (dgCoherentBarPrefixHom R D F s k (by omega))
    (by omega : (n : ℤ) + 0 - ((n + 1 : ℕ) : ℤ) = -1)
    (by omega : ((n + 1 : ℕ) : ℤ) + -(k : ℤ) -
      ((n + 1 - (k + 1) : ℕ) : ℤ) = 1) (show (-1 : ℤ) + 1 = 0 from rfl)
  have hu := compose_unit_of_heq (A := R) (D := RightModule R D)
    (dgCoherentBarPrefixHom R D F s k (by omega)) (unitElement R M).val
    rfl rfl rfl HEq.rfl
  exact hh.trans ((heq_of_eq hc).trans (block_degree_heq R D _ _ M N
    (zero_add (-(k : ℤ))) rfl _ _ hu _ _))

end SerrePositivity.InfinityCategories
