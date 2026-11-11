module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixDegeneracyNaturality
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarSource_tail_degeneracy_before {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k + 1 ≤ j.val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ j s) (k + 1) (by omega)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) (by omega)) := by
  have hp := congrArg (fun f => I.map f.op s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixOrder_degeneracy_before j (k + 1) hk)
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at hp
  have hv := congrArg (fun t : I _⦋k + 1⦌ => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F
    (I.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ (Fin.last (k + 1))).op t)) hp
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_target R D F (I.σ j s) k (by omega)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_target R D F s k (by omega)
  exact h₁.symm.trans (hv.trans h₂)

private lemma block_transport_heq (a b : ℤ)
    (M N M' N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (hM : M = M') (hN : N = N')
    {q p : ℤ} (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R M N q) (f' : _root_.SerrePositivity.DifferentialGraded.GradedHom R M' N' q)
    (hf : HEq f f') (hp : a + q - b = p) :
    HEq (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D a b f hp)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D a b f' hp) := by
  cases hM
  cases hN
  cases eq_of_heq hf
  rfl

private lemma block_degree_heq (a b : ℤ) (M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    {q q' p p' : ℤ} (hq : q = q') (hp : p = p')
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R M N q) (f' : _root_.SerrePositivity.DifferentialGraded.GradedHom R M N q') (hf : HEq f f')
    (ha : a + q - b = p) (hb : a + q' - b = p') :
    HEq (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D a b f ha) (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D a b f' hb) := by
  cases hq
  cases hp
  cases eq_of_heq hf
  rfl

lemma dgCoherentBarPrefixBlock_degeneracy_before_comp {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k + 1 ≤ j.val) :
    HEq (_root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracy s j)))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ j s) (k + 1) (by omega))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F (I.σ j s) k (by omega))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F s j) (show (-1 : ℤ) + 1 = 0 from rfl))
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D (n : ℤ) ((n + 1 - (k + 1) : ℕ) : ℤ)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k (by omega))
        (by omega : (n : ℤ) + -(k : ℤ) - ((n + 1 - (k + 1) : ℕ) : ℤ) = 0)) := by
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩
  let N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) (by omega))
  have hm := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSource_degeneracy R D F s j
  have hn := dgCoherentBarSource_tail_degeneracy_before R D F s j k hk
  have hb : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F (I.σ j s) k (by omega))
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ)
        ((n + 1 - (k + 1) : ℕ) : ℤ)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k (by omega))
        (by omega : ((n + 1 : ℕ) : ℤ) + -(k : ℤ) -
          ((n + 1 - (k + 1) : ℕ) : ℤ) = 1)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock
    exact block_transport_heq R D _ _ _ _ _ _ hm hn _ _
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixHom_degeneracy_before R D F s j k hk) _
  have hd : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F s j)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
        (_root_.SerrePositivity.DifferentialGraded.unitElement R M).val (by omega : (n : ℤ) + 0 - ((n + 1 : ℕ) : ℤ) = -1)) := by
    unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomTargetTransport R D _ _ _ _ _ _).property
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl (congrArg (_root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ)) hm)
    (congrArg (_root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 - (k + 1) : ℕ) : ℤ)) hn)
    rfl rfl rfl _ _ _ _ hb hd rfl rfl
  have hc := _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock_comp R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
    ((n + 1 - (k + 1) : ℕ) : ℤ)
    (unitElement R M).val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k (by omega))
    (by omega : (n : ℤ) + 0 - ((n + 1 : ℕ) : ℤ) = -1)
    (by omega : ((n + 1 : ℕ) : ℤ) + -(k : ℤ) -
      ((n + 1 - (k + 1) : ℕ) : ℤ) = 1) (show (-1 : ℤ) + 1 = 0 from rfl)
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_unit_of_heq (A := R) (D := RightModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k (by omega)) (unitElement R M).val
    rfl rfl rfl HEq.rfl
  exact hh.trans ((heq_of_eq hc).trans (block_degree_heq R D _ _ M N
    (zero_add (-(k : ℤ))) rfl _ _ hu _ _))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
