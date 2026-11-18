module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction

/-!
# 元の未縮約 hammock から縮約済みの代表への到達

概要：二つの基本縮約が止まる条件は原典の縮約条件であり、常に有限段で到達する。
方針：非交互の隣接二列または全行恒等の一列を縮約し、長さで帰納する。
規約：合流性・一意性は後続。元の余極限内の値も同じ代表へ保持する。
使われ方：縮約 hammock の正規形と実際の余極限の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) (n : SimplexCategoryᵒᵖ)

lemma no_reduction_of_reduced {r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n} (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y r)
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n} : ¬ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n r s := by
  intro h
  cases h with
  | merge d p hp τ => exact (hr.1 p.castSucc p.succ rfl) hp
  | erase j τ hτ => exact hr.2 j hτ

lemma exists_reduction_of_not_reduced (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n)
    (h : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y r) : ∃ s, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n r s := by
  classical
  obtain ⟨w, τ⟩ := r
  change ¬ ((∀ i j : Fin w.length, j.val = i.val + 1 → w.direction i ≠ w.direction j) ∧
    ∀ j : Fin w.length, ¬ ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj k) j) at h
  rcases not_and_or.mp h with ha | hi
  · simp only [not_forall, not_not] at ha
    obtain ⟨i, j, hij, hd⟩ := ha
    cases w with
    | mk l d =>
      cases l with
      | zero => exact Fin.elim0 i
      | succ l =>
        cases l with
        | zero =>
          have hi := i.isLt
          have hj := j.isLt
          change i.val < 1 at hi
          change j.val < 1 at hj
          omega
        | succ k =>
          let p : Fin (k + 1) := ⟨i.val, by
            have hj := j.isLt
            change j.val < k + 2 at hj
            omega⟩
          have hip : p.castSucc = i := Fin.ext rfl
          have hjp : p.succ = j := Fin.ext hij.symm
          have hp : d p.castSucc = d p.succ := by rw [hip, hjp]; exact hd
          exact ⟨_, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.merge d p hp τ⟩
  · obtain ⟨j, hj⟩ := not_forall.mp hi
    exact ⟨_, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.erase j τ (not_not.mp hj)⟩

/-- 元の縮約条件は、元の基本縮約ができないことと同値。 -/
lemma reduced_iff_no_reduction (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y r ↔ ∀ s, ¬ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n r s := by
  constructor
  · intro h s
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.no_reduction_of_reduced W X Y n h
  · intro h
    by_contra hr
    obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.exists_reduction_of_not_reduced W X Y n r hr
    exact h s hs

/-- 任意の元の全射列は有限回の基本縮約で縮約済みの代表へ到達する。 -/
lemma exists_reduced_representative (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    ∃ s, Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) r s ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y s := by
  classical
  refine (measure (fun r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n => r.1.length)).wf.induction
    (C := fun r => ∃ s, Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) r s ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y s) r ?_
  intro r ih
  by_cases hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y r
  · exact ⟨r, Relation.ReflTransGen.refl, hr⟩
  · obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.exists_reduction_of_not_reduced W X Y n r hr
    obtain ⟨t, ht, hred⟩ := ih s (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.length_lt hs)
    exact ⟨t, (Relation.ReflTransGen.single hs).trans ht, hred⟩

lemma exists_reduced_same_value (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    ∃ s, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y s ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y r = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y s := by
  obtain ⟨s, hs, hred⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.exists_reduced_representative W X Y n r
  exact ⟨s, hred, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.chain_value_eq hs⟩

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
