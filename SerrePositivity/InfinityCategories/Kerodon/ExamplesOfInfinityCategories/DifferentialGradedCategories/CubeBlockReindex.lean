module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeBlockPermutations
public import Mathlib.GroupTheory.Perm.Finite

/-!
# 全置換の和から区間内置換への再添字付け

概要：区間を保たない置換には逆転した座標の組があり、それらの値が零なら全和を二重和にできる。
方針：Fin の和へ移した置換の左右の保存を調べ、区間内置換の単射で和を移す。
規約：先頭区間の長さは p、末尾区間の長さは q。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0） の全ての最大旗の和の整理。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：区間内の二つの置換から全体の置換への写像は単射である。
方針：和の置換の単射性と同値による移送の単射性を合成する。
規約：組を一つの変数として扱う。
使われ方：Kerodon 2.5.8（Tag 00S0） の符号付き和の再添字付け。 -/
lemma cubeBlockPermutation_injective (p q : ℕ) :
    Function.Injective (fun s : Equiv.Perm (Fin p) × Equiv.Perm (Fin q) ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation s.1 s.2) := by
  intro a b h
  apply Equiv.Perm.sumCongrHom_injective
  exact finSumFinEquiv.permCongr.injective h

/-- 概要：Fin の和で先頭区間を保つ置換は二つの区間内置換から得られる。
方針：有限の和の置換が左の和を保存すれば和の置換となるという判定を使う。
規約：Fin の和への移送には finSumFinEquiv の逆を使う。
使われ方：HA 1.3.1.16 の全体の置換が適合することの判定。 -/
lemma cubeBlockPermutation_exists_of_mapsTo {p q : ℕ} (σ : Equiv.Perm (Fin (p + q)))
    (h : Set.MapsTo ((finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).permCongr.symm σ)
      (Set.range Sum.inl) (Set.range Sum.inl)) :
    ∃ a : Equiv.Perm (Fin p), ∃ b : Equiv.Perm (Fin q), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation a b = σ := by
  obtain ⟨⟨a, b⟩, hab⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl h
  refine ⟨a, b, ?_⟩
  exact (congrArg finSumFinEquiv.permCongr hab).trans
    (finSumFinEquiv.permCongr.apply_symm_apply σ)

/-- 概要：区間を保たない置換には後ろの座標が先の座標より前に現れる逆転がある。
方針：和の置換が左右を保存する条件の同値から、両方向に区間を越える座標を選ぶ。
規約：逆転の位置 r<s と、像の番号の p との大小を与える。
使われ方：Kerodon 2.5.8（Tag 00S0） の不適合な旗を退化で消すための逆転の検出。 -/
lemma cubeBlockPermutation_inversion_of_not_range {p q : ℕ}
    (σ : Equiv.Perm (Fin (p + q)))
    (hσ : σ ∉ Set.range (fun s : Equiv.Perm (Fin p) × Equiv.Perm (Fin q) ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation s.1 s.2)) :
    ∃ r s : Fin (p + q), r < s ∧ p ≤ (σ r).val ∧ (σ s).val < p := by
  classical
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  let π := e.permCongr.symm σ
  have hL : ¬ Set.MapsTo π (Set.range Sum.inl) (Set.range Sum.inl) := by
    intro h
    obtain ⟨a, b, hab⟩ := cubeBlockPermutation_exists_of_mapsTo σ h
    exact hσ ⟨(a, b), hab⟩
  have hR : ¬ Set.MapsTo π (Set.range Sum.inr) (Set.range Sum.inr) := by
    intro h
    exact hL ((Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr π).mpr h)
  have hL' : ∃ a : Fin p, π (Sum.inl a) ∉ Set.range Sum.inl := by
    simpa only [Set.MapsTo, Set.forall_mem_range, not_forall] using hL
  have hR' : ∃ b : Fin q, π (Sum.inr b) ∉ Set.range Sum.inr := by
    simpa only [Set.MapsTo, Set.forall_mem_range, not_forall] using hR
  obtain ⟨a, ha⟩ := hL'
  obtain ⟨b, hb⟩ := hR'
  cases ha' : π (Sum.inl a) with
  | inl c => exact False.elim (ha ⟨c, ha'.symm⟩)
  | inr c =>
    cases hb' : π (Sum.inr b) with
    | inr d => exact False.elim (hb ⟨d, hb'.symm⟩)
    | inl d =>
      have hπ (t : Fin p ⊕ Fin q) : e (π t) = σ (e t) := by
        simp only [π, Equiv.permCongr_symm_apply, e.apply_symm_apply]
      have ha'' : σ (Fin.castAdd q a) = Fin.natAdd p c := by
        simpa only [e, finSumFinEquiv_apply_left, ha', finSumFinEquiv_apply_right] using
          (hπ (Sum.inl a)).symm
      have hb'' : σ (Fin.natAdd p b) = Fin.castAdd q d := by
        simpa only [e, finSumFinEquiv_apply_left, hb', finSumFinEquiv_apply_right] using
          (hπ (Sum.inr b)).symm
      refine ⟨Fin.castAdd q a, Fin.natAdd p b, ?_, ?_, ?_⟩
      · change a.val < p + b.val
        have h := a.isLt
        omega
      · rw [ha'']
        change p ≤ p + c.val
        omega
      · rw [hb'']
        exact d.isLt

/-- 概要：区間外の置換で値が零なら、全置換の和は区間内置換の二重和である。
方針：区間内置換の単射と、その像の外での零を使って有限和を移す。
規約：係数は任意の可換加法モノイドでよい。
使われ方：HA 1.3.1.16 の全旗の和を左右の旗の和へ分ける。 -/
lemma cubeBlockPermutation_sum {M : Type*} [AddCommMonoid M] {p q : ℕ}
    (F : Equiv.Perm (Fin (p + q)) → M)
    (hF : ∀ σ ∉ Set.range (fun s : Equiv.Perm (Fin p) × Equiv.Perm (Fin q) ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation s.1 s.2), F σ = 0) :
    (∑ σ, F σ) = ∑ a : Equiv.Perm (Fin p), ∑ b : Equiv.Perm (Fin q),
      F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation a b) := by
  have h := Fintype.sum_of_injective
    (fun s : Equiv.Perm (Fin p) × Equiv.Perm (Fin q) ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation s.1 s.2)
    (cubeBlockPermutation_injective p q) _ F hF (fun _ ↦ rfl)
  rw [Fintype.sum_prod_type] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
