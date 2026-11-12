module
public import SerrePositivity.KST.SConstruction.SimplexHAZeroChainLift
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeSimplex

/-! # 元の実 dg 関手の零次元 HA 鎖射による回収
概要：元の実 dg 関手から抽出した HA 単体の零次元の逆鎖射は、元の語の実像に戻る。
方針：元の生成元値の回収式と元の HA 辺の計算を、零次元の全生成元判定で合成する。
規約：元の語の実鎖射との一致。使われ方：標準面との同定へ接続する逆律の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の実 dg 関手からの HA 単体の零次元の逆鎖射は、元の同じ語の実鎖射像。 -/
lemma simplexHAZeroChainLift_recovery {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (v : Fin 1 ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v 0 < b) :
    simplexHAZeroChainLift A (cubicalLambdaNativeSimplex A F) v b hb =
      simplexHABeadWordCell A (simplexHAGeneratorWord 0 PUnit.unit v b hb) ≫
        F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) := by
  apply serreCube_generator_hom_ext A 0
  intro i
  have hi : i = PUnit.unit := by cases i; rfl
  subst i
  change (simplexHAZeroChainLift A (cubicalLambdaNativeSimplex A F) v b hb).f 0
    (serreCubeTopCell A 0) = _
  exact (simplexHAZeroChainLift_top A (cubicalLambdaNativeSimplex A F) v b hb).trans
    ((simplexHAGeneratorValue_zero A (cubicalLambdaNativeSimplex A F) PUnit.unit v b hb).symm.trans
      (simplexHAGeneratorValue_recovery A F 0 PUnit.unit v b hb))

end SerrePositivity.KST.SConstruction
