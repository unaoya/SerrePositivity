module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeDeleteZeroFace
public import SerrePositivity.KST.SConstruction.SimplexHAInverseFunctorRecovery
public import SerrePositivity.KST.SConstruction.SimplexHAChainLiftFaces

/-! # 元の逆 dg 関手の部分集合 cell 回収と頂点削除
概要：全区間で実 cell 像を回収し、元の全零面による内部頂点削除へ回収式を移す。
方針：元の両 cell・HA 鎖射の零面制限と、実 dg 関手の全 Hom の端点移送を照合する。
規約：削除前の回収式の入力を明記。使われ方：全区間から任意部分集合への有限帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma map_heq {C : Type u} [EnrichedCategory (Complex A) C]
    (F : EnrichedFunctor (Complex A) C D) {x x' y y' : C} (hx : x = x') (hy : y = y') :
    HEq (F.map x y) (F.map x' y') := by
  cases hx
  cases hy
  rfl

/-- 元の全区間部分集合 cell の逆 dg 関手による像は、同じ全区間 HA 実鎖射。 -/
lemma simplexHAInverseFunctor_cell_strictInterval {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) (hab : a < b) :
    simplexHADecodeSubsetCell A (b.val - a.val - 1) (simplexHAStrictIntervalOrder a b hab)
        {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ simplexHAStrictIntervalOrder_last_lt a b hab) ≫
      (simplexHAInverseFunctor A s).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
        simplexHAIntervalChainLift A s a b hab := by
  have h := (simplexHAInverseFunctor_map_vertices A s a b).trans
    (simplexHAHomMap_of_lt A s a b hab)
  exact (congrArg (fun f => f ≫ (simplexHAInverseFunctor A s).map
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
      (simplexHADecodeSubsetCell_strictInterval A a b hab)).trans
        ((congrArg (fun f => (simplexIntervalLambdaHomIso A a b hab.le).hom ≫ f) h).trans
          (simplexHAIntervalHomMap_restrict A s a b hab))

/-- 元の cell 像の回収式は、同じ内部頂点を除く任意座標の零面へ移る。 -/
lemma simplexHAInverseFunctor_cell_delete {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (m : ℕ) (q : Fin (m + 1)) (v : Fin (m + 2) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (m + 1)) < b)
    (hfull : simplexHADecodeSubsetCell A (m + 1) v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) ≫
        (simplexHAInverseFunctor A s).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      simplexHAChainLift A s (m + 1) v b hb) :
    simplexHADecodeSubsetCell A m (simplexHADeleteVertexOrder m q v) {b}
        (Finset.singleton_nonempty b) (simplexHADeleteVertexOrder_bound m q v {b}
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)) ≫
      (simplexHAInverseFunctor A s).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (simplexHADeleteVertexOrder m q v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      simplexHAChainLift A s m (simplexHADeleteVertexOrder m q v) b
        ((v.monotone (Fin.le_last _)).trans_lt hb) := by
  let F := simplexHAInverseFunctor A s
  let w := simplexHADeleteVertexOrder m q v
  have hx := simplexHADeleteVertexOrder_first m q v
  have hc := simplexHADecodeSubsetCell_delete_zero_face_heq A m q v b hb
  have hmap := map_heq A F (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex.{u}) hx.symm)
    (rfl : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex.{u} b = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)
  have hcomp := heq_comp (rfl : serreCubeComplex A m = serreCubeComplex A m)
    (congrArg (fun a : Fin (N + 1) => homObject A
      (CubicalLambda A (Δ[N] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
        hx.symm)
    (congrArg (fun a => homObject A D (s.obj a) (s.obj b)) hx.symm) hc hmap
  have hp := congrArg (fun f => (serreCubeFace A false m q).hom ≫ f) hfull
  have hz := simplexHAChainLift_zero_face A s m q v b hb
  exact eq_of_heq (hcomp.symm.trans
    ((heq_of_eq ((Category.assoc _ _ _).trans hp)).trans
      ((heq_of_eq hz).trans (comp_eqToHom_heq _ _))))

end SerrePositivity.KST.SConstruction
