module
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorBoundary
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordBoundaryZero
public import SerrePositivity.KST.SConstruction.SerreCubeZeroGeneratorDifferential

/-! # 元の全零次数生成元上の HA 微分可換性
概要：任意次元の零次数 tensor 生成元上で、元の HA 線形復元は実微分と可換。
方針：元の生成元の閉性と零自由次元語の境界零性を、指定次数の全生成元式で合わせる。
規約：零次元 cube だけに制限しない。使われ方：全自由次元に関する微分条件の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 任意の元の HA データについて、零次数生成元に対応する境界評価は零。 -/
lemma simplexHAGeneratorBoundaryValue_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (hi : serreCubeGeneratorDegree m i = 0)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    simplexHAGeneratorBoundaryValue A s m i v b hb = 0 := by
  have hf : serreCubeGeneratorFreeDimension m i = 0 := by
    have h := serreCubeGeneratorDegree_freeDimension m i
    omega
  have h := congrArg (fun w => eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
    (congrArg (fun k : ℤ => k + 1) (serreCubeGeneratorDegree_freeDimension m i).symm)) w)
      (simplexHABeadWordBoundaryValue_zero A s (simplexHAGeneratorWord m i v b hb) hf)
  exact h.trans (map_zero _)

/-- 任意次元の元の全零次数 tensor 生成元上で、元の HA 線形復元は実微分と可換。 -/
lemma simplexHADegreeLift_zero_generator_comm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (hi : serreCubeGeneratorDegree m i = 0)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    (homObject A D (s.obj (v 0)) (s.obj b)).d 0 1
        (simplexHADegreeLift A s.toSimplexData m v b hb 0
          (eqToHom (congrArg (fun k => (serreCubeComplex A m).X k) hi)
            (serreCubeGenerator A m i))) =
      simplexHADegreeLift A s.toSimplexData m v b hb 1 ((serreCubeComplex A m).d 0 1
        (eqToHom (congrArg (fun k => (serreCubeComplex A m).X k) hi)
          (serreCubeGenerator A m i))) := by
  have h := simplexHADegreeLift_generator_differential A s m v b hb 0 i hi
  have hz := congrArg (fun w => eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
    (congrArg (fun k : ℤ => k + 1) hi)) w)
      (simplexHAGeneratorBoundaryValue_zero A s.toSimplexData m i hi v b hb)
  have hs := congrArg (fun w => simplexHADegreeLift A s.toSimplexData m v b hb 1 w)
    (serreCubeGenerator_zero_d A m i hi)
  exact (h.trans (hz.trans (map_zero _))).trans (hs.trans (map_zero _)).symm

/-- 任意次元の元の cube の全零次数加群で、元の HA 線形復元は実微分と可換。 -/
lemma simplexHADegreeLift_zero_comm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) :
    simplexHADegreeLift A s.toSimplexData m v b hb 0 ≫
        (homObject A D (s.obj (v 0)) (s.obj b)).d 0 1 =
      (serreCubeComplex A m).d 0 1 ≫ simplexHADegreeLift A s.toSimplexData m v b hb 1 := by
  apply serreCube_degree_hom_ext A m 0
  intro i hi
  exact simplexHADegreeLift_zero_generator_comm A s m i hi v b hb

end SerrePositivity.KST.SConstruction
