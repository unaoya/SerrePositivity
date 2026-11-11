module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinExtremeFaceCongruence

/-!
概要：join の整合する最初・最後の面を混合単体へ貼り合わせる。
方針：最後の面の左因子と最初の面の右因子を取り、共通の面の等式で両端を検査する。
規約：切断の差は一、因子の移送は cast と HEq で明示する。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、join の混合した内ホーンの充填。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：整合する最初・最後の面は一つの混合 join 単体へ貼り合わさる。
方針：左因子を最後の面、右因子を最初の面から取り、面の制限を比較する。
規約：a が最初の面、b が最後の面で、両者の切断の差は一。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、quasicategory の join の内ホーンの充填。 -/
lemma Join.Simplex.exists_extreme_faces {X Y : SSet.{u}} {n : ℕ}
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 1)) (hc : b.1.val = a.1.val + 1)
    (hab : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom b) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 2), s.1.val = b.1.val ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 3))).toOrderHom s = a ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom s = b := by
  have hb : b.1.val ≤ n + 2 := by have := b.1.isLt; omega
  have ha : a.1.val ≤ n + 1 := by omega
  have hb0 : 0 < b.1.val := by omega
  have hr : n + 2 - a.1.val = n + 3 - b.1.val := by omega
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 2) :=
    ⟨⟨b.1.val, by omega⟩, b.2.1, cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj Y) hr) a.2.2⟩
  have hs0 : 0 < s.1.val := hb0
  have hs1 : s.1.val ≤ n + 2 := hb
  have hsl : HEq s.2.1 b.2.1 := HEq.rfl
  have hsr : HEq s.2.2 a.2.2 := cast_heq _ _
  have hzero : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 3))).toOrderHom s).1 = a.1 := by
    apply Fin.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ (0 : Fin (n + 3))).toOrderHom b.1.val = a.1.val
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_zero (n + 1) b.1.val hb0 (by omega)
    omega
  have hlast : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom s).1 = b.1 := by
    apply Fin.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_last (n + 1) b.1.val hb
  refine ⟨s, rfl, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ hzero
    · have hh : HEq
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom b).2.1
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom a).2.1 := by rw [hab]
      have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.delta_zero_left_heq_of_left_heq s b rfl hs0 hsl).trans
        (hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq a ha))
      exact eq_of_heq ((cast_heq _ _).trans he)
    · have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_zero_right_heq s hs0).trans hsr
      exact eq_of_heq ((cast_heq _ _).trans he)
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ hlast
    · have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq s hs1).trans hsl
      exact eq_of_heq ((cast_heq _ _).trans he)
    · have hh : HEq
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom a).2.2
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom b).2.2 := by rw [hab]
      have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.delta_last_right_heq_of_right_heq s a hr.symm hs1 ha hsr).trans
        (hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_zero_right_heq b hb0))
      exact eq_of_heq ((cast_heq _ _).trans he)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
