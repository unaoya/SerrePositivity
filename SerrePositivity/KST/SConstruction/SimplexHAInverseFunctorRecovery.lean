module
public import SerrePositivity.KST.SConstruction.SimplexHAIntervalDecodeCell
public import SerrePositivity.KST.SConstruction.SimplexHAInverseFunctor

/-! # 元の実 dg 関手からの native HA 逆構成の回収
概要：元の実 dg 関手を native HA 単体にして復元すると、元の全対象・全 Hom が戻る。
方針：厳密区間の全頂点生成射と Hom 同型、対角の可逆単位、逆向き零 Hom を使う。
規約：元の実 dg 関手と全次数を保持。使われ方：native HA 単体比較の一方の逆律。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の実 dg 関手の厳密区間の HA 鎖射復元は、同じ Hom 比較に制限した元の作用。 -/
lemma simplexHAIntervalChainLift_native {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (a b : Fin (N + 1)) (hab : a < b) :
    simplexHAIntervalChainLift A (cubicalLambdaNativeSimplex A F) a b hab =
      (simplexIntervalLambdaHomIso A a b hab.le).hom ≫
        F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  (simplexHAChainLift_map_recovery A F (b.val - a.val - 1)
    (simplexHAStrictIntervalOrder a b hab) b (simplexHAStrictIntervalOrder_last_lt a b hab)).trans
      (congrArg (fun f => f ≫ F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
        (simplexHADecodeSubsetCell_strictInterval A a b hab))

/-- 元の実 dg 関手の厳密区間 Hom の復元は、元の同じ全次数 Hom 作用。 -/
lemma simplexHAIntervalHomMap_native {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (a b : Fin (N + 1)) (hab : a < b) :
    simplexHAIntervalHomMap A (cubicalLambdaNativeSimplex A F) a b hab =
      F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) := by
  exact (congrArg (fun f => (simplexIntervalLambdaHomIso A a b hab.le).inv ≫ f)
    (simplexHAIntervalChainLift_native A F a b hab)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
          (simplexIntervalLambdaHomIso A a b hab.le).inv_hom_id).trans (Category.id_comp _)))

/-- 元の実 dg 関手の全頂点間 Hom の復元は、元の同じ全次数 Hom 作用。 -/
lemma simplexHAHomMap_native {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D) (a b : Fin (N + 1)) :
    simplexHAHomMap A (cubicalLambdaNativeSimplex A F) a b =
      F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact (simplexHAHomMap_of_lt A (cubicalLambdaNativeSimplex A F) a b hab).trans
      (simplexHAIntervalHomMap_native A F a b hab)
  · exact (simplexHAHomMap_self A (cubicalLambdaNativeSimplex A F) a).trans
      (simplexLambdaDiagonalMap_recovery A F a)
  · exact (simplexReverseLambdaHom_isZero A a b hba).eq_of_src _ _

/-- 元の実 dg 関手からの復元は、元の全対象の作用を回収する。 -/
lemma simplexHAInverseFunctor_native_obj {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (x : CubicalLambda A (Δ[N] : SSet.{u})) :
    (simplexHAInverseFunctor A (cubicalLambdaNativeSimplex A F)).obj x = F.obj x := by
  obtain ⟨a, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective x
  rfl

/-- 元の実 dg 関手を native HA 単体にして復元すると、元の実 dg 関手が厳密に戻る。 -/
lemma simplexHAInverseFunctor_native {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D) :
    simplexHAInverseFunctor A (cubicalLambdaNativeSimplex A F) = F := by
  refine EnrichedFunctor.ext (Complex A)
    (F := simplexHAInverseFunctor A (cubicalLambdaNativeSimplex A F)) (G := F)
    (simplexHAInverseFunctor_native_obj A F) ?_
  intro x y
  obtain ⟨a, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective x
  obtain ⟨b, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective y
  exact (Category.comp_id _).trans
    ((simplexHAInverseFunctor_map_vertices A (cubicalLambdaNativeSimplex A F) a b).trans
      (simplexHAHomMap_native A F a b))

/-- 元の全 native HA 成分が一致する実 dg 関手は、全対象・全 Hom で厳密に一致する。 -/
lemma cubicalLambdaNativeSimplex_injective (N : ℕ) :
    Function.Injective (fun F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D =>
      cubicalLambdaNativeSimplex A F) := by
  intro F G h
  exact (simplexHAInverseFunctor_native A F).symm.trans
    ((congrArg (simplexHAInverseFunctor A) h).trans (simplexHAInverseFunctor_native A G))

end SerrePositivity.KST.SConstruction
