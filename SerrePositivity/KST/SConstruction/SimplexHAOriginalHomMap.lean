module
public import SerrePositivity.KST.SConstruction.SimplexHAHomMap

/-! # 元の Λ の全対象・全 Hom 上の native HA 復元族
概要：元の零単体を対象とする Λ の全 Hom に、元の HA Hom 鎖射族を移す。
方針：元の零単体と頂点番号の実逆対応と、元の Hom 対象の等号だけで移送する。
規約：元の対象型と全 Hom を保持。使われ方：合成保存を接続する実逆 dg 関手のデータ。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の標準単体の頂点番号と、元の Λ の全対象との実逆対応。 -/
def simplexLambdaVertexEquiv (N : ℕ) : Fin (N + 1) ≃ CubicalLambda A (Δ[N] : SSet.{u}) where
  toFun := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex
  invFun x := (cubicalLambdaVertexEquiv A (Δ[N] : SSet.{u}) x) 0
  left_inv _ := rfl
  right_inv x := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_eta x

/-- 元の Λ の各対象に、元の同じ頂点の HA 対象を対応させる。 -/
def simplexHAInverseObj {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (x : CubicalLambda A (Δ[N] : SSet.{u})) : D := s.obj ((simplexLambdaVertexEquiv A N).symm x)

/-- 元の Λ の全 Hom に、元の HA 値を持つ実 Hom 鎖射を与える。 -/
def simplexHAOriginalHomMap {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (x y : CubicalLambda A (Δ[N] : SSet.{u})) :
    homObject A (CubicalLambda A (Δ[N] : SSet.{u})) x y ⟶
      homObject A D (simplexHAInverseObj A s x) (simplexHAInverseObj A s y) :=
  eqToHom (congrArg₂ (fun x y : CubicalLambda A (Δ[N] : SSet.{u}) =>
    homObject A (CubicalLambda A (Δ[N] : SSet.{u})) x y)
      ((simplexLambdaVertexEquiv A N).apply_symm_apply x).symm
      ((simplexLambdaVertexEquiv A N).apply_symm_apply y).symm) ≫
    simplexHAHomMap A s ((simplexLambdaVertexEquiv A N).symm x)
      ((simplexLambdaVertexEquiv A N).symm y)

/-- 元の番号の頂点での対象復元は、元の HA 対象そのもの。 -/
lemma simplexHAInverseObj_vertex {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (a : Fin (N + 1)) :
    simplexHAInverseObj A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) = s.obj a := rfl

/-- 元の番号の頂点での Hom 復元は、元の同じ全 Hom 鎖射族そのもの。 -/
lemma simplexHAOriginalHomMap_vertices {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) :
    simplexHAOriginalHomMap A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      simplexHAHomMap A s a b := Category.id_comp _

/-- 元の Λ の全対象の実単位は、同じ HA 対象の実単位へ写る。 -/
lemma simplexHAOriginalHomMap_id {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (x : CubicalLambda A (Δ[N] : SSet.{u})) :
    eId (Complex A) x ≫ simplexHAOriginalHomMap A s x x =
      eId (Complex A) (simplexHAInverseObj A s x) := by
  obtain ⟨a, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective x
  exact (congrArg (fun f => eId (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) ≫ f) (simplexHAOriginalHomMap_vertices A s a a)).trans
      (simplexHAHomMap_id A s a)

/-- 元の Λ の全対象・全 Hom の復元族は、厳密 dg 関手による後合成と可換。 -/
lemma simplexHAOriginalHomMap_post {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E)
    (x y : CubicalLambda A (Δ[N] : SSet.{u})) :
    simplexHAOriginalHomMap A (s.map F) x y =
      simplexHAOriginalHomMap A s x y ≫
        F.map (simplexHAInverseObj A s x) (simplexHAInverseObj A s y) := by
  obtain ⟨a, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective x
  obtain ⟨b, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective y
  exact (simplexHAOriginalHomMap_vertices A (s.map F) a b).trans
    ((simplexHAHomMap_post A s F a b).trans
      (congrArg (fun f => f ≫ F.map (s.obj a) (s.obj b))
        (simplexHAOriginalHomMap_vertices A s a b)).symm)

end SerrePositivity.KST.SConstruction
