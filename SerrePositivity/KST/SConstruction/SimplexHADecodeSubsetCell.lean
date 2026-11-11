module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCoordinate
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaCellAtDimension

/-! # 元の読み替え部分集合の同端点・同次元の実生成射
概要：昇順列と右側集合の元の部分集合から、読み替えと同じ次元の実 Serre 鎖射を作る。
方針：元の濃度次元と両端点の回収式を、元の同端点部分集合生成射へ適用する。
規約：元の実鎖射と頂点を保持。使われ方：読み替えの語と元の標準面の帰納的比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の読み替え部分集合の同端点の実生成射を、同じ読み替え次元から読む。 -/
def simplexHADecodeSubsetCell {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    serreCubeComplex A (m + T.card - 1) ⟶ homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (T.max' hT)) :=
  simplexSubsetLambdaCellAtDimension A (simplexHADecodeSubset m v T) (v 0) (T.max' hT)
    (simplexHADecodeSubset_two m v T hT hb) (simplexHADecodeSubset_min m v T hb).symm
    (simplexHADecodeSubset_max m v T hT hb).symm (m + T.card - 1)
    (simplexHADecodeSubset_dimension m v T hb).symm

/-- 元の読み替え次元の実鎖射は、元の同じ部分集合の実生成射と異種等号で一致する。 -/
lemma simplexHADecodeSubsetCell_canonical_heq {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    HEq (simplexHADecodeSubsetCell A m v T hT hb)
      (simplexSubsetLambdaCell A (simplexHADecodeSubset m v T)
        (simplexHADecodeSubset_two m v T hT hb)) :=
  simplexSubsetLambdaCellAtDimension_canonical_heq A _ _ _ _ _ _ _ _

/-- 元の読み替え部分集合が等しければ、元の同端点・同次元の実生成射は異種等号で一致。 -/
lemma simplexHADecodeSubsetCell_congr_heq {n : ℕ} (m m' : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (v' : Fin (m' + 1) ↪o Fin (n + 1))
    (T T' : Finset (Fin (n + 1))) (hT : T.Nonempty) (hT' : T'.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last m) < t) (hb' : ∀ t ∈ T', v' (Fin.last m') < t)
    (h : simplexHADecodeSubset m v T = simplexHADecodeSubset m' v' T') :
    HEq (simplexHADecodeSubsetCell A m v T hT hb)
      (simplexHADecodeSubsetCell A m' v' T' hT' hb') :=
  (simplexHADecodeSubsetCell_canonical_heq A m v T hT hb).trans
    ((simplexSubsetLambdaCell_heq_of_eq A _ _ h _ _).trans
      (simplexHADecodeSubsetCell_canonical_heq A m' v' T' hT' hb').symm)

end SerrePositivity.KST.SConstruction
