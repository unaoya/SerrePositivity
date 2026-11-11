module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordBoundary
public import SerrePositivity.KST.SConstruction.SimplexHADegreeLift
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImageDifferentialTransport

/-! # 元の全 HA 生成元値の境界評価と微分
概要：元の全 tensor 生成元の読み替え語の境界値を指定次数へ移し、値の微分と同定する。
方針：全 bead 語の境界評価と、元の微分・線形復元の次数移送を合成する。
規約：境界評価は HA 右辺から構成。使われ方：元の生成元微分の線形復元像との比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の生成元読み替え語の HA 境界値を、元の生成元の微分次数へ移す。 -/
def simplexHAGeneratorBoundaryValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    GradedHom A (s.obj (v 0)) (s.obj b) (serreCubeGeneratorDegree m i + 1) :=
  eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
    (congrArg (fun k : ℤ => k + 1) (serreCubeGeneratorDegree_freeDimension m i).symm))
      (simplexHABeadWordBoundaryValue A s (simplexHAGeneratorWord m i v b hb))

/-- 任意の元の native HA 単体について、全生成元値の微分は同じ読み替え語の境界評価。 -/
lemma simplexHAGeneratorValue_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    differential A (simplexHAGeneratorValue A s.toSimplexData m i v b hb) =
      simplexHAGeneratorBoundaryValue A s.toSimplexData m i v b hb :=
  (complexDifferential_degree_transport A (homObject A D (s.obj (v 0)) (s.obj b))
    (serreCubeGeneratorDegree_freeDimension m i).symm
    (congrArg (fun k : ℤ => k + 1) (serreCubeGeneratorDegree_freeDimension m i).symm) _).trans
      (congrArg (fun w => eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
        (congrArg (fun k : ℤ => k + 1) (serreCubeGeneratorDegree_freeDimension m i).symm)) w)
          (simplexHABeadWordRawValue_differential A s (simplexHAGeneratorWord m i v b hb)))

/-- 元の任意次数の生成元上で、線形復元値の微分は元の境界評価の指定次数への移送。 -/
lemma simplexHADegreeLift_generator_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) (k : ℤ) (i : SerreCubeGeneratorIndex m)
    (hi : serreCubeGeneratorDegree m i = k) :
    (homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1)
        (simplexHADegreeLift A s.toSimplexData m v b hb k
          (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
            (serreCubeGenerator A m i))) =
      eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
        (congrArg (fun d : ℤ => d + 1) hi))
          (simplexHAGeneratorBoundaryValue A s.toSimplexData m i v b hb) := by
  have h := congrArg (fun w => (homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1) w)
    (simplexHADegreeLift_generator A s.toSimplexData m v b hb k i hi)
  exact h.trans ((complexDifferential_degree_transport A
    (homObject A D (s.obj (v 0)) (s.obj b)) hi (congrArg (fun d : ℤ => d + 1) hi) _).trans
      (congrArg (fun w => eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
        (congrArg (fun d : ℤ => d + 1) hi)) w)
          (simplexHAGeneratorValue_differential A s m i v b hb)))

end SerrePositivity.KST.SConstruction
