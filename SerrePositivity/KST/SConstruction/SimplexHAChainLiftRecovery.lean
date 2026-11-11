module
public import SerrePositivity.KST.SConstruction.SimplexHAChainLift
public import SerrePositivity.KST.SConstruction.SimplexHADegreeMapRecovery
public import SerrePositivity.KST.SConstruction.SimplexHADegreeNaturality
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeSimplex

/-! # 元の実 HA Hom 鎖射の回収と厳密 dg 後合成自然性
概要：元の実 dg 関手からの復元は同じ Hom 射を回収し、dg 後合成と可換。
方針：元の全次数の線形復元の回収・自然性を、実鎖射の全成分で判定する。
規約：元の全生成元と実射を保持。使われ方：逆 dg 関手と native 比較の逆律。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の全生成元の HA 値を回収する実 Hom 鎖射は、元の同じ標準復元鎖射に一致する。 -/
lemma simplexHAChainLift_eq {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b)
    (F : serreCubeComplex A m ⟶ homObject A D (s.obj (v 0)) (s.obj b))
    (hF : ∀ i : SerreCubeGeneratorIndex m,
      simplexHAGeneratorValue A s.toSimplexData m i v b hb =
        F.f (serreCubeGeneratorDegree m i) (serreCubeGenerator A m i)) :
    simplexHAChainLift A s m v b hb = F := by
  apply serreCube_generator_hom_ext A m
  intro i
  exact (simplexHAChainLift_generator A s m v b hb _ i rfl).trans (hF i)

/-- 元の実 dg 関手からの native HA 単体の復元は、元の部分集合生成射の同じ実像。 -/
lemma simplexHAChainLift_map_recovery {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) :
    simplexHAChainLift A (cubicalLambdaNativeSimplex A F) m v b hb =
      simplexHADecodeSubsetCell A m v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) ≫
          F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact simplexHADegreeLift_map_recovery A F m v b hb k

/-- 元の実 Hom 鎖射の復元は、元の厳密 dg 関手による後合成と厳密に可換。 -/
lemma simplexHAChainLift_post {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) :
    simplexHAChainLift A (s.map F) m v b hb =
      simplexHAChainLift A s m v b hb ≫ F.map (s.obj (v 0)) (s.obj b) := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact simplexHADegreeLift_post A s.toSimplexData F m v b hb k

/-- 元の零次元の標準実復元は、既存の元の HA 辺の閉性による鎖射と一致する。 -/
lemma simplexHAChainLift_zero {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (v : Fin 1 ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v 0 < b) :
    simplexHAChainLift A s 0 v b hb = simplexHAZeroChainLift A s v b hb := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact simplexHADegreeLift_zero_eq_chain A s v b hb k

end SerrePositivity.KST.SConstruction
