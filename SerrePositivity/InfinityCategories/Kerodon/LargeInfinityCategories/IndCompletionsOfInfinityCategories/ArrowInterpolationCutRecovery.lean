module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ArrowInterpolationCoconeCoordinates

/-!
概要：全円柱への比較の像から補間余錐の切断を復元する。
方針：切断前では新しい終端頂点を避け、切断以降ではその頂点へ送られる。
規約：任意の試験形状・退化単体を含む。使われ方：比較の単射性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 補間領域の空次数を補った余錐座標。 -/
def arrowInterpolationAugX (A : SSet.{u}) (r : ℕ)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) r) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin A Δ[0] r :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv A Δ[0] r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫ fst _ _) r q)

/-- 補間領域の空次数を補った区間座標。 -/
def arrowInterpolationAugY (A : SSet.{u}) (r : ℕ)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) r) : Fin r →o Fin 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 1 r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫ snd _ _) r q)

/-- 補間領域では余錐点の上の区間座標は零。 -/
lemma arrowInterpolationAug_vertex (A : SSet.{u}) (r : ℕ)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) r) (i : Fin r)
    (hi : (arrowInterpolationAugX A r q).1.val ≤ i.val) :
    arrowInterpolationAugY A r q i = 0 := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion_vertex q i hi

/-- 比較後の余錐座標の切断は、元の補間単体の内側の切断。 -/
lemma arrowInterpolationCocone_cut {A : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) Δ[0] n) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A).app (Opposite.op ⦋n⦌) s).1.1.val =
      (arrowInterpolationAugX A s.1.val s.2.1).1.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationConeFold_cut _

/-- 切断前の区間座標は、元の補間単体の座標。 -/
lemma arrowInterpolationCocone_y_lt {A : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) Δ[0] n)
    (i : Fin (n + 1)) (hi : i.val < s.1.val) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A).app (Opposite.op ⦋n⦌) s).2 i =
      arrowInterpolationAugY A s.1.val s.2.1 ⟨i.val, hi⟩ :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_lt 1 n _ i hi

/-- 切断以降の区間座標は終点。 -/
lemma arrowInterpolationCocone_y_ge {A : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) Δ[0] n)
    (i : Fin (n + 1)) (hi : s.1.val ≤ i.val) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A).app (Opposite.op ⦋n⦌) s).2 i = 1 :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_ge 1 n _ i hi

/-- 比較の像の各頂点が新しい終端頂点以外であることから切断位置を復元できる。 -/
lemma arrowInterpolationCocone_vertex_iff {A : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) Δ[0] n) (i : Fin (n + 1)) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A).app (Opposite.op ⦋n⦌) s).1.1.val ≤ i.val →
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A).app (Opposite.op ⦋n⦌) s).2 i ≠ 1) ↔ i.val < s.1.val := by
  by_cases hi : i.val < s.1.val
  · refine iff_of_true ?_ hi
    intro ha
    rw [arrowInterpolationCocone_cut] at ha
    rw [arrowInterpolationCocone_y_lt s i hi,
      arrowInterpolationAug_vertex A _ _ ⟨i.val, hi⟩ ha]
    decide
  · refine iff_of_false ?_ hi
    intro hh
    have hc := (arrowInterpolationAugX A s.1.val s.2.1).1.isLt
    have ha : ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A).app (Opposite.op ⦋n⦌) s).1.1.val ≤ i.val := by
      rw [arrowInterpolationCocone_cut]
      omega
    exact hh ha (arrowInterpolationCocone_y_ge s i (Nat.le_of_not_gt hi))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
