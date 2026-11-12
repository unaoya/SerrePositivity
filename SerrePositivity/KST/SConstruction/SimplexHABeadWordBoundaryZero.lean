module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordBoundary
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackEquation

/-! # 元の零自由次元 bead 語の境界と閉性
概要：任意の HA データの零自由次元語の境界評価は零で、HA 単体では生の値が閉じる。
方針：二点集合の HA 右辺の零性と連結の元の境界評価を帰納する。
規約：元の全零自由次元語を保持。使われ方：零次数生成元上の微分可換性の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 任意の元の HA データについて、零自由次元語の境界評価は零。 -/
lemma simplexHABeadWordBoundaryValue_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b : Fin (n + 1)} {d : ℕ} (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) :
    d = 0 → simplexHABeadWordBoundaryValue A s word = 0 := by
  induction word with
  | bead I hI =>
    intro hd
    have hc : I.card = 2 := by omega
    exact (congrArg (fun w => serreCubeOrientationSign (I.card - 2) • w)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_of_card_two s I _ _ _ hI rfl rfl (by omega) hc)).trans (smul_zero _)
  | @join a b c p q left right ihL ihR =>
    intro hd
    have hl := ihL (by omega)
    have hr := ihR (by omega)
    change forward A (simplexHABeadWordBoundaryValue A s left)
        (simplexHABeadWordRawValue A s right) (by omega) +
      (-(p : ℤ)).negOnePow • forward A (simplexHABeadWordRawValue A s left)
        (simplexHABeadWordBoundaryValue A s right) (by omega) = 0
    rw [hl, hr]
    simp only [forward, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero,
      smul_zero, add_zero]

/-- 任意の元の native HA 単体について、零自由次元語の生の値は閉じている。 -/
lemma simplexHABeadWordRawValue_closed {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    {a b : Fin (n + 1)} {d : ℕ} (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) (hd : d = 0) :
    differential A (simplexHABeadWordRawValue A s.toSimplexData word) = 0 :=
  (simplexHABeadWordRawValue_differential A s word).trans
    (simplexHABeadWordBoundaryValue_zero A s.toSimplexData word hd)

end SerrePositivity.KST.SConstruction
