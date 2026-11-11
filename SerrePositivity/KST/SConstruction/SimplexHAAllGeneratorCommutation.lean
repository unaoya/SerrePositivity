module
public import SerrePositivity.KST.SConstruction.SimplexHAChainLiftExistence

/-! # 元の native HA 線形復元の全生成元上の実微分可換性
概要：零・一端点と辺を任意に混在させた全生成元で、元の線形復元と微分が可換。
方針：強い次元帰納で得た実 Hom 鎖射の全次数回収から、元の微分差の零性を得る。
規約：元の全生成元と実 source 微分を保持。使われ方：標準の鎖射復元への無条件入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 任意の元の native HA 単体について、全次数の元の微分合成の差は零。 -/
lemma simplexHADegreeDefect_zero {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) (k : ℤ) :
    simplexHADegreeDefect A s.toSimplexData m v b hb k = 0 := by
  obtain ⟨F, hF⟩ := simplexHAChainLift_exists A s m v b hb
  exact simplexHADegreeDefect_zero_of_chain A s.toSimplexData m v b hb F hF k

/-- 元の全次数の線形復元は、元の実 source・target 微分と可換。 -/
lemma simplexHADegreeLift_comm {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) (k : ℤ) :
    simplexHADegreeLift A s.toSimplexData m v b hb k ≫
      (homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1) =
      (serreCubeComplex A m).d k (k + 1) ≫
        simplexHADegreeLift A s.toSimplexData m v b hb (k + 1) :=
  sub_eq_zero.mp (simplexHADegreeDefect_zero A s m v b hb k)

/-- 元の全端点・辺生成元について、任意指定次数で元の実微分可換性を得る。 -/
lemma simplexHADegreeLift_generator_comm {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (N + 1))
    (b : Fin (N + 1)) (hb : v (Fin.last m) < b) (k : ℤ)
    (hi : serreCubeGeneratorDegree m i = k) :
    (homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1)
      (simplexHADegreeLift A s.toSimplexData m v b hb k
        (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
          (serreCubeGenerator A m i))) =
      simplexHADegreeLift A s.toSimplexData m v b hb (k + 1)
        ((serreCubeComplex A m).d k (k + 1)
          (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
            (serreCubeGenerator A m i))) :=
  ConcreteCategory.congr_hom (simplexHADegreeLift_comm A s m v b hb k) _

/-- 元の全生成元の source 微分像は、元の独立に定義した HA 語境界値と一致する。 -/
lemma simplexHADegreeLift_generator_source_boundary {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (N + 1))
    (b : Fin (N + 1)) (hb : v (Fin.last m) < b) (k : ℤ)
    (hi : serreCubeGeneratorDegree m i = k) :
    simplexHADegreeLift A s.toSimplexData m v b hb (k + 1)
      ((serreCubeComplex A m).d k (k + 1)
        (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
          (serreCubeGenerator A m i))) =
      eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
        (congrArg (fun d : ℤ => d + 1) hi))
        (simplexHAGeneratorBoundaryValue A s.toSimplexData m i v b hb) :=
  (simplexHADegreeLift_generator_comm A s m i v b hb k hi).symm.trans
    (simplexHADegreeLift_generator_differential A s m v b hb k i hi)

end SerrePositivity.KST.SConstruction
