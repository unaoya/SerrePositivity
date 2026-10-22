module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePrefixDetermination
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCornerImage

/-!
概要：全円柱の単体を補間領域と終端頂点に分ける切断。
方針：余錐座標の切断と区間の零座標の切断の最大を取る。
規約：元の全単体を保持。使われ方：補間余錐比較の全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 区間の単体の零頂点からなる先頭区間の長さ。 -/
def intervalZeroCut {n : ℕ} (t : (Δ[1] : SSet.{u}) _⦋n⦌) : ℕ :=
  Join.pullCut (Join.stdAugEquiv 1 (n + 1) t) 1

/-- 区間の零切断より前の座標は零。 -/
lemma intervalZeroCut_lt {n : ℕ} (t : (Δ[1] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) (hi : i.val < intervalZeroCut t) : t i = 0 := by
  have h := (Join.lt_pullCut_iff (Join.stdAugEquiv 1 (n + 1) t) 1 i).mp hi
  apply Fin.ext
  change (t i).val < 1 at h
  change (t i).val = 0
  omega

/-- 区間の零切断以降の座標は一。 -/
lemma intervalZeroCut_ge {n : ℕ} (t : (Δ[1] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) (hi : intervalZeroCut t ≤ i.val) : t i = 1 := by
  unfold intervalZeroCut at hi
  have h : ¬ (Join.stdAugEquiv 1 (n + 1) t i).val < 1 := by
    intro h
    have := (Join.lt_pullCut_iff (Join.stdAugEquiv 1 (n + 1) t) 1 i).mpr h
    omega
  apply Fin.ext
  change ¬ (t i).val < 1 at h
  have := (t i).isLt
  change (t i).val = 1
  omega

/-- 全円柱の単体の終端頂点を除く先頭の長さ。 -/
def arrowPrismCut {A : SSet.{u}} {n : ℕ}
    (s : (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌) : ℕ :=
  max s.1.1.val (intervalZeroCut s.2)

/-- この切断は元の単体の頂点数を超えない。 -/
lemma arrowPrismCut_le {A : SSet.{u}} {n : ℕ}
    (s : (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌) : arrowPrismCut s ≤ n + 1 :=
  max_le (Nat.le_of_lt_succ s.1.1.isLt) (Join.pullCut_le _ _)

/-- 切断前の全単体は、実補間領域の単体として持ち上がる。 -/
lemma exists_arrowPrism_prefix_lift {A : SSet.{u}} {n : ℕ}
    (s : (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌) :
    ∃ q : Join.augObj (arrowInterpolationCorner A) (arrowPrismCut s),
      Join.augHom (arrowInterpolationCornerInclusion A) (arrowPrismCut s) q =
        Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ Δ[1])
          (Join.prefixIncl (n + 1) (arrowPrismCut s) (arrowPrismCut_le s)) s := by
  suffices ∀ r (hr : arrowPrismCut s = r) (hle : r ≤ n + 1),
      ∃ q : Join.augObj (arrowInterpolationCorner A) r,
        Join.augHom (arrowInterpolationCornerInclusion A) r q =
          Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ Δ[1])
            (Join.prefixIncl (n + 1) r hle) s from this _ rfl (arrowPrismCut_le s)
  intro r hr hle
  cases r with
  | zero => exact ⟨PUnit.unit, rfl⟩
  | succ r =>
    let α := Join.prefixIncl (n + 1) (r + 1) hle
    let z := Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) α s
    apply (arrowInterpolationCornerInclusion_range_iff z).mpr
    by_cases h : intervalZeroCut s.2 ≤ s.1.1.val
    · left
      have ha : r + 1 = s.1.1.val := hr.symm.trans (max_eq_left h)
      change (stableAugJoinEquiv A Δ[0] (r + 1) (Join.augMap (join A Δ[0]) α s.1)).1.val = _
      rw [joinSimplex_prefix_cut, ha, Nat.min_self]
    · right
      have hb : r + 1 = intervalZeroCut s.2 :=
        hr.symm.trans (max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h)))
      intro i
      change Join.stdAugEquiv 1 (r + 1) (Join.augMap (Δ[1] : SSet.{u}) α s.2) i = 0
      rw [Join.stdAugEquiv_augMap]
      exact intervalZeroCut_lt s.2 (α i) (by
        change i.val < intervalZeroCut s.2
        rw [← hb]
        exact i.isLt)

end SerrePositivity.InfinityCategories.F2.Ind
