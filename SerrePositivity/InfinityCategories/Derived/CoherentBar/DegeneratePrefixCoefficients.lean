module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateCuts
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeDegeneracy
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomotopyImage
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
/-!
概要：重複二頂点を含む長さ二以上の prefix の実 bar 係数は零になる。
方針：元の単体ラベルの退化性を、全高次成分の零性と線形な shift ブロックへ送る。
規約：元の coherentDiagramTop と端点輸送を保持する。長さ一の単位項は別に扱う。
使われ方：同じ theta が退化部分を保存することの高次 prefix 項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixHom_degenerate_zero {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (h : k + 1 ≤ n + 1)
    (hk : 1 ≤ k) (hj : j.val + 1 ≤ k + 1) :
    dgCoherentBarPrefixHom R D F (I.σ j s) k h = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    have hd := dgCoherentBar_prefix_degenerate s j (k + 2) h hj
    have hz := dgCoherentBar_native_top_transported_eq_zero_of_degenerate F
      (dgCoherentBarPrefix (I.σ j s) (k + 2) h).2 hd
    unfold dgCoherentBarPrefixHom
    rw [hz]
    exact map_zero _

lemma dgCoherentBarPrefixBlock_degenerate_zero {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (h : k + 1 ≤ n + 1)
    (hk : 1 ≤ k) (hj : j.val + 1 ≤ k + 1) :
    dgCoherentBarPrefixBlock R D F (I.σ j s) k h = 0 := by
  unfold dgCoherentBarPrefixBlock
  rw [dgCoherentBarPrefixHom_degenerate_zero R D F s j k h hk hj]
  exact moduleHomShiftBlock_zero R D _ _ _ _ _ _ _

set_option maxHeartbeats 800000 in
-- 正規化直和の全 Hom end と切断ラベルの依存型を照合する。
lemma dgCoherentBarPrefixColumn_degenerate_normalizedProjection {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) (k : ℕ) (h : k + 1 ≤ n + 1)
    (hj : j.val ≠ 0 ∨ k ≠ 0) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩)
      (dgCoherentBarNormalizedProjection R D F)).f 1
      (dgCoherentBarPrefixColumn R D F (I.σ j s) k h) = 0 := by
  by_cases ht : k + 1 ≤ j.val
  · exact dgCoherentBarDegenerateTargetColumn_normalizedProjection R D F ⟨n + 1, I.σ j s⟩
      ⟨dgCoherentBarTail (I.σ j s) (k + 1) h,
        dgCoherentBar_tail_degenerate s j (k + 1) h ht⟩
      1 (dgCoherentBarPrefixBlock R D F (I.σ j s) k h)
  · have hk : 1 ≤ k := by omega
    have hprefix : j.val + 1 ≤ k + 1 := by omega
    unfold dgCoherentBarPrefixColumn
    rw [dgCoherentBarPrefixBlock_degenerate_zero R D F s j k h hk hprefix,
      map_zero, map_zero]

end SerrePositivity.InfinityCategories
