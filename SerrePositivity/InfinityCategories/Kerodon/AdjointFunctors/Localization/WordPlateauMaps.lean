module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPlateauColumn

/-!
# 同じ切断の fiber 上の元の縦射の一致

概要：語の作用の像の間の縦射は、同じ切断を持つ全頂点で異種等しい。
方針：挿入恒等列の可換正方形を使い、有限区間の長さで帰納する。
規約：単射性は要求せず、元の全縦射を保持する。
使われ方：語の包含の遷移関手の充満性と像の特徴付け。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} (f : a ⟶ b) {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y}

/-- 向きに応じた二点の異種等式を、元の左から右の二点へ戻す。 -/
lemma source_target_heq {I : Type*} {M : I → Sort*} (m : ∀ i, M i)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I)
    (h : HEq (m (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.source d p q)) (m (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.target d p q))) : HEq (m p) (m q) := by
  cases d
  · exact h
  · exact h.symm

lemma app_cut_eq_adjacent (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) (j : Fin b.length)
    (h : f.cut j.castSucc = f.cut j.succ) : HEq (g.app j.castSucc) (g.app j.succ) := by
  have he := f.cut_source_target_of_eq j h
  have hc := g.comm j
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f S j ≫ g.app (b.target j) = g.app (b.source j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f T j at hc
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column_eqToHom_of_cut_eq f S j h he, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column_eqToHom_of_cut_eq f T j h he] at hc
  have hh : HEq (g.app (b.target j)) (g.app (b.source j)) := by
    have hh := heq_of_eq hc
    simpa only [eqToHom_comp_heq_iff, heq_comp_eqToHom_iff] using hh
  exact source_target_heq (fun k => g.app k) (b.direction j) j.castSucc j.succ hh.symm

lemma app_cut_eq_of_le (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) (p q : Fin (b.length + 1))
    (hpq : p ≤ q) (h : f.cut p = f.cut q) : HEq (g.app p) (g.app q) := by
  induction q using Fin.induction generalizing p with
  | zero =>
    have hp : p = 0 := le_antisymm hpq (Fin.zero_le p)
    subst p
    rfl
  | succ q ih =>
    by_cases hp : p = q.succ
    · subst p
      rfl
    · have hp' : p ≤ q.castSucc := by
        have hne : p.val ≠ q.val + 1 := fun he => hp (Fin.ext he)
        change p.val ≤ q.val + 1 at hpq
        change p.val ≤ q.val
        omega
      have hmid : f.cut q.castSucc = f.cut q.succ := by
        apply le_antisymm (f.cut_monotone (Fin.castSucc_le_succ q))
        rw [← h]
        exact f.cut_monotone hp'
      exact (ih p hp' (h.trans hmid.symm)).trans (app_cut_eq_adjacent f g q hmid)

/-- 同じ切断の全 fiber 上で、元の縦射の成分は一致する。 -/
lemma app_cut_eq (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) (p q : Fin (b.length + 1))
    (h : f.cut p = f.cut q) : HEq (g.app p) (g.app q) := by
  rcases le_total p q with hpq | hqp
  · exact app_cut_eq_of_le f g p q hpq h
  · exact (app_cut_eq_of_le f g q p hqp h.symm).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
