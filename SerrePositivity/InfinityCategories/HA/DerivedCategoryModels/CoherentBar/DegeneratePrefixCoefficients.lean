module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateCuts
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeDegeneracy
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomotopyImage
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixHom_degenerate_zero {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (h : k + 1 ≤ n + 1)
    (hk : 1 ≤ k) (hj : j.val + 1 ≤ k + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F (I.σ j s) k h = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    have hd := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_prefix_degenerate s j (k + 2) h hj
    have hz := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_native_top_transported_eq_zero_of_degenerate F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix (I.σ j s) (k + 2) h).2 hd
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom
    rw [hz]
    exact map_zero _

lemma dgCoherentBarPrefixBlock_degenerate_zero {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (h : k + 1 ≤ n + 1)
    (hk : 1 ≤ k) (hj : j.val + 1 ≤ k + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F (I.σ j s) k h = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock
  rw [dgCoherentBarPrefixHom_degenerate_zero R D F s j k h hk hj]
  exact _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock_zero R D _ _ _ _ _ _ _

set_option maxHeartbeats 800000 in
-- 正規化直和の全 Hom end と切断ラベルの依存型を照合する。
lemma dgCoherentBarPrefixColumn_degenerate_normalizedProjection {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) (k : ℕ) (h : k + 1 ≤ n + 1)
    (hj : j.val ≠ 0 ∨ k ≠ 0) :
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F (I.σ j s) k h) = 0 := by
  by_cases ht : k + 1 ≤ j.val
  · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateTargetColumn_normalizedProjection R D F ⟨n + 1, I.σ j s⟩
      ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ j s) (k + 1) h,
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_tail_degenerate s j (k + 1) h ht⟩
      1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F (I.σ j s) k h)
  · have hk : 1 ≤ k := by omega
    have hprefix : j.val + 1 ≤ k + 1 := by omega
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn
    rw [dgCoherentBarPrefixBlock_degenerate_zero R D F s j k h hk hprefix,
      map_zero, map_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
