module
public import SerrePositivity.KST.SConstruction.SimplexHARawWordComposition

/-! # 元の HA bead 語の境界評価
概要：部分集合 bead の HA 右辺と連結の Leibniz 則から、元の語の境界値を評価する。
方針：bead は元の向き付き HA 右辺、連結は同じ豊穣順と第一因子次数の符号で再帰する。
規約：境界評価の定義には微分を使わない。使われ方：元の生成元境界との読み替え比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の HA 右辺と豊穣順 Leibniz 則で独立に定めた、元の bead 語の境界評価。 -/
def simplexHABeadWordBoundaryValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) :
    {a b : Fin (n + 1)} → {d : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d →
      GradedHom A (s.obj a) (s.obj b) (-(d : ℤ) + 1)
  | _, _, _, .bead I hI => serreCubeOrientationSign (I.card - 2) •
      s.rhs I _ _ (-((I.card - 2 : ℕ) : ℤ)) hI rfl rfl (by omega)
  | _, _, _, .join (p := p) left right =>
      forward A (simplexHABeadWordBoundaryValue s left) (simplexHABeadWordRawValue A s right)
        (by omega) +
      (-(p : ℤ)).negOnePow • forward A (simplexHABeadWordRawValue A s left)
        (simplexHABeadWordBoundaryValue s right) (by omega)

/-- 元の連結語の生の値の微分は、元の豊穣順と第一因子次数の Leibniz 則を回収する。 -/
lemma simplexHABeadWordRawValue_join_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b c : Fin (n + 1)} {p q : ℕ} (left : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b p)
    (right : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n b c q) :
    differential A (simplexHABeadWordRawValue A s (left.join right)) =
      forward A (differential A (simplexHABeadWordRawValue A s left))
        (simplexHABeadWordRawValue A s right) (by omega) +
      (-(p : ℤ)).negOnePow • forward A (simplexHABeadWordRawValue A s left)
        (differential A (simplexHABeadWordRawValue A s right)) (by omega) :=
  (congrArg (differential A) (simplexHABeadWordRawValue_join A s left right)).trans
    (differential_forward A (simplexHABeadWordRawValue A s left)
      (simplexHABeadWordRawValue A s right) (by omega))

private lemma differential_units_smul {x y : D} {k : ℤ} (e : ℤˣ)
    (f : GradedHom A x y k) : differential A (e • f) = e • differential A f := by
  change (homObject A D x y).d k (k + 1) (e • f) =
    e • (homObject A D x y).d k (k + 1) f
  simp only [Units.smul_def, map_zsmul]

/-- 任意の元の native HA 単体について、全 bead 語の生の値の微分は元の境界評価。 -/
lemma simplexHABeadWordRawValue_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    {a b : Fin (n + 1)} {d : ℕ} (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) :
    differential A (simplexHABeadWordRawValue A s.toSimplexData word) =
      simplexHABeadWordBoundaryValue A s.toSimplexData word := by
  induction word with
  | bead I hI =>
    exact (differential_units_smul A (serreCubeOrientationSign (I.card - 2)) _).trans
      (congrArg (fun w => serreCubeOrientationSign (I.card - 2) • w)
        (s.equation I _ _ (-((I.card - 2 : ℕ) : ℤ)) hI rfl rfl (by omega)))
  | @join a b c p q left right ihL ihR =>
    exact (simplexHABeadWordRawValue_join_differential A s.toSimplexData left right).trans
      (congrArg₂ (fun x y => forward A x (simplexHABeadWordRawValue A s.toSimplexData right)
        (show (-(p : ℤ) + 1) + -(q : ℤ) = -((p + q : ℕ) : ℤ) + 1 by omega) +
        (-(p : ℤ)).negOnePow • forward A (simplexHABeadWordRawValue A s.toSimplexData left) y
          (show -(p : ℤ) + (-(q : ℤ) + 1) = -((p + q : ℕ) : ℤ) + 1 by omega)) ihL ihR)

end SerrePositivity.KST.SConstruction
