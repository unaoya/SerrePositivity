module
public import SerrePositivity.KST.SConstruction.SimplexHAZeroFaceAllDefect
public import SerrePositivity.KST.SConstruction.SerreCubeZeroEdgeIndex
public import SerrePositivity.KST.SConstruction.SimplexHATopAllDimensions
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorBoundary

/-! # 元の零端点と辺が混在する全生成元上の実微分可換性
概要：零端点と辺だけを含む任意の元の生成元で、元の HA 線形復元と微分が可換。
方針：最高生成元上の HA 方程式を基底に、任意座標の零面制限で次元帰納する。
規約：実 source 微分と全指定次数を保持。使われ方：全生成元の逆 Hom 鎖射条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の全次元の最高生成元で、元の二つの微分合成の差は零。 -/
lemma simplexHADegreeDefect_top_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) :
    simplexHADegreeDefect A s.toSimplexData m v b hb (-(m : ℤ)) (serreCubeTopCell A m) = 0 := by
  change (homObject A D (s.obj (v 0)) (s.obj b)).d (-(m : ℤ)) (-(m : ℤ) + 1)
    (simplexHADegreeLift A s.toSimplexData m v b hb (-(m : ℤ)) (serreCubeTopCell A m)) -
      simplexHADegreeLift A s.toSimplexData m v b hb (-(m : ℤ) + 1)
        ((serreCubeComplex A m).d (-(m : ℤ)) (-(m : ℤ) + 1) (serreCubeTopCell A m)) = 0
  exact sub_eq_zero.mpr (simplexHADegreeLift_top_comm_all A s m v b hb)

/-- 元の最高添字の生成元の差は、任意指定次数へ移しても零。 -/
lemma simplexHADegreeDefect_top_generator_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) (k : ℤ)
    (hi : serreCubeGeneratorDegree m (serreCubeTopGeneratorIndex m) = k) :
    simplexHADegreeDefect A s.toSimplexData m v b hb k
      (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
        (serreCubeGenerator A m (serreCubeTopGeneratorIndex m))) = 0 := by
  have hk : -(m : ℤ) = k := (serreCubeTopGeneratorIndex_degree m).symm.trans hi
  cases hk
  exact (congrArg (fun x => simplexHADegreeDefect A s.toSimplexData m v b hb (-(m : ℤ)) x)
    (serreCubeTopGeneratorIndex_cast A m)).trans (simplexHADegreeDefect_top_zero A s m v b hb)

/-- 元の零端点と辺だけを含む全生成元で、元の二つの微分合成の差は零。 -/
lemma simplexHADegreeDefect_zeroEdge_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (hie : SerreCubeZeroEdgeIndex m i)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) (k : ℤ) (hi : serreCubeGeneratorDegree m i = k) :
    simplexHADegreeDefect A s.toSimplexData m v b hb k
      (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
        (serreCubeGenerator A m i)) = 0 := by
  induction m generalizing b k with
  | zero =>
    cases i
    exact simplexHADegreeDefect_top_generator_zero A s 0 v b hb k hi
  | succ m ih =>
    rcases serreCubeZeroEdgeIndex_cases m i hie with rfl | ⟨q, j, hj, rfl⟩
    · exact simplexHADegreeDefect_top_generator_zero A s (m + 1) v b hb k hi
    · have hp : serreCubeGeneratorDegree m j = k :=
        (serreCubeInsertGeneratorIndex_degree false m q j).symm.trans hi
      let w := simplexHADeleteVertexOrder m q v
      let hw := (v.monotone
        (Fin.le_last ((simplexHAFaceVertex m q).succAbove (Fin.last m)))).trans_lt hb
      let E : homObject A D (s.obj (w 0)) (s.obj b) ⟶ homObject A D (s.obj (v 0)) (s.obj b) :=
        eqToHom (congrArg (fun a => homObject A D (s.obj a) (s.obj b))
          (simplexHADeleteVertexOrder_first m q v))
      have h := simplexHADegreeDefect_insert_zero A s.toSimplexData m q j v b hb k hp
      have ht := congrArg (fun x => E.f (k + 1) x) (ih j hj w b hw k hp)
      exact h.trans (ht.trans (map_zero _))

/-- 元の零端点と辺が混在する全生成元で、元の source・target 微分は実際に可換。 -/
lemma simplexHADegreeLift_zeroEdge_generator_comm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (hie : SerreCubeZeroEdgeIndex m i)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) (k : ℤ) (hi : serreCubeGeneratorDegree m i = k) :
    (homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1)
      (simplexHADegreeLift A s.toSimplexData m v b hb k
        (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
          (serreCubeGenerator A m i))) =
      simplexHADegreeLift A s.toSimplexData m v b hb (k + 1)
        ((serreCubeComplex A m).d k (k + 1)
          (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
            (serreCubeGenerator A m i))) :=
  sub_eq_zero.mp (simplexHADegreeDefect_zeroEdge_zero A s m i hie v b hb k hi)

/-- 元の零端点と辺の全生成元の source 微分像は、独立に定義した元の HA 境界値。 -/
lemma simplexHADegreeLift_zeroEdge_source_boundary {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (hie : SerreCubeZeroEdgeIndex m i)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) (k : ℤ) (hi : serreCubeGeneratorDegree m i = k) :
    simplexHADegreeLift A s.toSimplexData m v b hb (k + 1)
      ((serreCubeComplex A m).d k (k + 1)
        (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
          (serreCubeGenerator A m i))) =
      eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
        (congrArg (fun d : ℤ => d + 1) hi))
        (simplexHAGeneratorBoundaryValue A s.toSimplexData m i v b hb) :=
  (simplexHADegreeLift_zeroEdge_generator_comm A s m i hie v b hb k hi).symm.trans
    (simplexHADegreeLift_generator_differential A s m v b hb k i hi)

end SerrePositivity.KST.SConstruction
