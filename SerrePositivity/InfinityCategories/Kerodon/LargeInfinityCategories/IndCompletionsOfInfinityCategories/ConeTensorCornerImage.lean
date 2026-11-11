module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeTensorCocone

/-!
概要：補間領域の像を二つの余錐座標の切断で特徴づける。
方針：pushout の全単体の被覆と元の包含の像を照合する。
規約：任意の元の両形状と全境界を保持し、有限性を要求しない。
使われ方：有限半順序形状の点追加における相対補間。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：補間領域の像を二つの余錐座標の切断で特徴づける。
方針：pushout の全単体の被覆と元の包含の像を照合する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorCornerInclusion_range_iff {A L : SSet.{u}} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L Δ[0]) _⦋n⦌) :
    (∃ q, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion A L).app (Opposite.op ⦋n⦌) q = s) ↔
      s.1.1.val = n + 1 ∨ s.2.1.val = n + 1 := by
  constructor
  · rintro ⟨q, rfl⟩
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pushout_simplex_covered (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ▷ L) (Opposite.op ⦋n⦌) q with ⟨b, rfl⟩ | ⟨c, rfl⟩
    · have he := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_old A L) (Opposite.op ⦋n⦌)) b
      erw [he]
      exact Or.inl rfl
    · have he := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_lower A L) (Opposite.op ⦋n⦌)) c
      erw [he]
      exact Or.inr rfl
  · rintro (h | h)
    · obtain ⟨a, ha⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplex_inl_iff s.1).mpr h
      refine ⟨(pushout.inl (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ▷ L)).app _ (a, s.2), ?_⟩
      change ((pushout.inl _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion A L).app
        (Opposite.op ⦋n⦌)) (a, s.2) = s
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_old]
      exact Prod.ext ha rfl
    · obtain ⟨b, hb⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplex_inl_iff s.2).mpr h
      refine ⟨(pushout.inr (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ▷ L)).app _ (s.1, b), ?_⟩
      change ((pushout.inr _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion A L).app
        (Opposite.op ⦋n⦌)) (s.1, b) = s
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_lower]
      exact Prod.ext rfl hb
/-- 概要：補間領域の像を二つの余錐座標の切断で特徴づける。
方針：pushout の全単体の被覆と元の包含の像を照合する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorCornerInclusion_max_cut {A L : SSet.{u}} {n : ℕ}
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCorner A L) _⦋n⦌) :
    max (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion A L).app (Opposite.op ⦋n⦌) q).1.1.val)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion A L).app (Opposite.op ⦋n⦌) q).2.1.val) = n + 1 := by
  rcases (coneTensorCornerInclusion_range_iff _).mp ⟨q, rfl⟩ with h | h
  · rw [h]
    exact max_eq_left (Nat.le_of_lt_succ
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion A L).app (Opposite.op ⦋n⦌) q).2.1.isLt))
  · rw [h]
    exact max_eq_right (Nat.le_of_lt_succ
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion A L).app (Opposite.op ⦋n⦌) q).1.1.isLt))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
