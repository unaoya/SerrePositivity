module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConePrefix
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAugmented

/-!
概要：余錐の単体は、その切断を含む先頭区間への制限で決まる。
方針：制限の切断は二つの長さの最小値。さらに元の切断まで制限して左単体を回収。
規約：空次数も含む。使われ方：全円柱比較の全射性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 先頭区間に沿う切断の逆像は二つの長さの最小値。 -/
lemma pullCut_prefix (n r : ℕ) (hr : r ≤ n) (a : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl n r hr) a = min r a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _) (Nat.min_le_left _ _)
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff, lt_min_iff]
  exact ⟨fun h => ⟨i.isLt, h⟩, fun h => h.2⟩

/-- 先頭制限の切断は元の切断と先頭の長さの最小値。 -/
lemma joinSimplex_prefix_cut (A B : SSet.{u}) (n r : ℕ) (hr : r ≤ n + 1)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv A B r
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (n + 1) r hr) s)).1.val = min r s.1.val := by
  cases r with
  | zero => simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv, Equiv.coe_fn_mk, Nat.zero_min]; rfl
  | succ r => exact pullCut_prefix (n + 1) (r + 1) hr s.1.val

/-- 切断を含む先頭制限が同じなら、余錐の元の全単体が一致する。 -/
lemma coneSimplex_eq_of_prefix {A : SSet.{u}} {n r : ℕ} (hr : r ≤ n + 1)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A (Δ[0] : SSet.{u}) n)
    (hs : s.1.val ≤ r) (ht : t.1.val ≤ r)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (n + 1) r hr) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (n + 1) r hr) t) : s = t := by
  have hc := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv A (Δ[0] : SSet.{u}) r z).1.val) h
  rw [joinSimplex_prefix_cut, joinSimplex_prefix_cut,
    Nat.min_eq_right hs, Nat.min_eq_right ht] at hc
  have he : s.1 = t.1 := Fin.ext hc
  rcases s with ⟨ℓ, x, y⟩
  rcases t with ⟨ℓ', x', y'⟩
  dsimp only at he hs
  subst ℓ'
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ rfl ?_ ?_
  · change x = x'
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})) ℓ.val
    have hp := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl r ℓ.val hs)) h
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_comp] at hp
    have hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (n + 1) r hr).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl r ℓ.val hs) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt) := rfl
    rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.joinSimplex_prefix, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.joinSimplex_prefix] at hp
    exact hp
  · change y = y'
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 _).injective
    apply DFunLike.ext
    intro i
    exact (by decide : ∀ a b : Fin 1, a = b) _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
