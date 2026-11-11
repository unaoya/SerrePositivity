module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordMerge
public import Mathlib.Data.Fintype.Card
public import Lean.Elab.Tactic.Omega

/-!
# 元の交互方向語の分類とその始域からの写像

概要：交互方向語は初めの向きで決まり、そこからの元の語の写像は全て単射である。
方針：二つの向きの反転と Fin の隣接位置での単射判定を使う。
規約：空語も含む。等しい長さでは語の等式と元の射の一致まで回収する。
使われ方：長さ濾過の段階に付け加える二つの交互方向語。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

namespace Direction

def other : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction
  | .forward => .backward
  | .backward => .forward

lemma ne_other (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) : d ≠ other d := by cases d <;> decide

lemma eq_other_of_ne {d e : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} (h : d ≠ e) : e = other d := by
  cases d <;> cases e <;> simp_all [other]

def alternatingSequence (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction
  | 0 => d
  | n + 1 => other (alternatingSequence d n)

end Direction
namespace Word

def IsAlternating (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : Prop :=
  ∀ i j : Fin a.length, j.val = i.val + 1 → a.direction i ≠ a.direction j

/-- 二つの初期方向で与える、任意の長さの元の交互方向語。 -/
def alternating (n : ℕ) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word :=
  ⟨n, fun i => d.alternatingSequence i.val⟩

lemma alternating_isAlternating (n : ℕ) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) : IsAlternating (alternating n d) := by
  intro i j hij
  change d.alternatingSequence i.val ≠ d.alternatingSequence j.val
  rw [hij]
  exact Direction.ne_other _

lemma IsAlternating.map_injective {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (ha : IsAlternating a) (f : a ⟶ b) :
    Function.Injective f.orderHom := by
  cases a with
  | mk l d =>
    cases l with
    | zero => intro i; exact Fin.elim0 i
    | succ k =>
      apply (Fin.orderHom_injective_iff f.orderHom).2
      intro p hp
      exact ha p.castSucc p.succ rfl ((f.direction_eq p.castSucc).symm.trans
        ((congrArg b.direction hp).trans (f.direction_eq p.succ)))

lemma IsAlternating.length_le {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (ha : IsAlternating a) (f : a ⟶ b) :
    a.length ≤ b.length := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f.orderHom (ha.map_injective f)

lemma alternating_direction_eq {n : ℕ} (d : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (ha : IsAlternating (⟨n + 1, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)) (i : Fin (n + 1)) :
    d i = (d 0).alternatingSequence i.val := by
  refine Fin.induction rfl (fun p ih => ?_) i
  exact (Direction.eq_other_of_ne (ha p.castSucc p.succ rfl)).trans (congrArg Direction.other ih)

lemma exists_alternating (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : IsAlternating a) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction, a = alternating a.length d := by
  cases a with
  | mk n d =>
    cases n with
    | zero => exact ⟨.forward, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext _ _ rfl (fun i => Fin.elim0 i)⟩
    | succ n =>
      refine ⟨d 0, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext _ _ rfl ?_⟩
      exact alternating_direction_eq d ha

lemma alternating_cases (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : IsAlternating a) :
    a = alternating a.length .forward ∨ a = alternating a.length .backward := by
  obtain ⟨d, hd⟩ := exists_alternating a ha
  cases d with
  | forward => exact Or.inl hd
  | backward => exact Or.inr hd

lemma alternating_ne (n : ℕ) :
    alternating (n + 1) .forward ≠ alternating (n + 1) .backward := by
  intro h
  have he := (eqToHom h : alternating (n + 1) .forward ⟶
    alternating (n + 1) .backward).direction_eq (0 : Fin (n + 1))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.eqToHom_apply] at he
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.backward = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.forward at he
  cases he

lemma IsAlternating.target_eq_of_length_le {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (ha : IsAlternating a)
    (f : a ⟶ b) (hb : b.length ≤ a.length) : ∃ h : a = b, f = eqToHom h := by
  have hn := Nat.le_antisymm (ha.length_le f) hb
  have hf := ha.map_injective f
  have hs : Function.Surjective f.orderHom := by
    by_contra h
    have hc := Fintype.card_lt_of_injective_not_surjective f.orderHom hf h
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨h, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embedding_eq_of_range f (𝟙 b) hf Function.injective_id
    (by rw [Set.range_eq_univ.mpr hs]; exact Set.range_id.symm)
  exact ⟨h, by simpa only [Category.comp_id] using he.symm⟩

end Word
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
