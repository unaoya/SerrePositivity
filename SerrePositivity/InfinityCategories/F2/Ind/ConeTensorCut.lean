module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCornerImage
public import SerrePositivity.InfinityCategories.F2.Ind.ConePrefixDetermination

/-!
概要：余錐の積の全単体を元の補間領域と余錐点に分ける。
方針：二つの切断の最大値まで制限して、元の実境界に持ち上げる。
規約：任意の元の両形状と全境界を保持し、有限性を要求しない。
使われ方：有限半順序形状の点追加における相対補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：余錐の積の全単体を元の補間領域と余錐点に分ける。
方針：二つの切断の最大値まで制限して、元の実境界に持ち上げる。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
def coneTensorCut {A L : SSet.{u}} {n : ℕ}
    (s : (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0]) _⦋n⦌) : ℕ :=
  max s.1.1.val s.2.1.val
/-- 概要：余錐の積の全単体を元の補間領域と余錐点に分ける。
方針：二つの切断の最大値まで制限して、元の実境界に持ち上げる。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorCut_le {A L : SSet.{u}} {n : ℕ}
    (s : (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0]) _⦋n⦌) : coneTensorCut s ≤ n + 1 :=
  max_le (Nat.le_of_lt_succ s.1.1.isLt) (Nat.le_of_lt_succ s.2.1.isLt)
/-- 概要：余錐の積の全単体を元の補間領域と余錐点に分ける。
方針：二つの切断の最大値まで制限して、元の実境界に持ち上げる。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma exists_coneTensor_prefix_lift {A L : SSet.{u}} {n : ℕ}
    (s : (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0]) _⦋n⦌) :
    ∃ q : Join.augObj (coneTensorCorner A L) (coneTensorCut s),
      Join.augHom (coneTensorCornerInclusion A L) (coneTensorCut s) q =
        Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0])
          (Join.prefixIncl (n + 1) (coneTensorCut s) (coneTensorCut_le s)) s := by
  suffices ∀ r (hr : coneTensorCut s = r) (hle : r ≤ n + 1),
      ∃ q : Join.augObj (coneTensorCorner A L) r,
        Join.augHom (coneTensorCornerInclusion A L) r q =
          Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0])
            (Join.prefixIncl (n + 1) r hle) s from this _ rfl (coneTensorCut_le s)
  intro r hr hle
  cases r with
  | zero => exact ⟨PUnit.unit, rfl⟩
  | succ r =>
    let α := Join.prefixIncl (n + 1) (r + 1) hle
    let z := Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0]) α s
    apply (coneTensorCornerInclusion_range_iff z).mpr
    by_cases h : s.2.1.val ≤ s.1.1.val
    · left
      have ha : r + 1 = s.1.1.val := hr.symm.trans (max_eq_left h)
      change (stableAugJoinEquiv A Δ[0] (r + 1)
        (Join.augMap (join A Δ[0]) α s.1)).1.val = _
      rw [joinSimplex_prefix_cut, ha, Nat.min_self]
    · right
      have hb : r + 1 = s.2.1.val := hr.symm.trans (max_eq_right (Nat.le_of_not_ge h))
      change (stableAugJoinEquiv L Δ[0] (r + 1)
        (Join.augMap (join L Δ[0]) α s.2)).1.val = _
      rw [joinSimplex_prefix_cut, hb, Nat.min_self]

end SerrePositivity.InfinityCategories.F2.Ind
