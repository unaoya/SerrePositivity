module
public import SerrePositivity.KST.SConstruction.SimplexHAInverseNativeDecodedComponent
public import SerrePositivity.KST.SConstruction.SimplexHASubsetPrefixOrder

/-! # 元の native HA 単体への逆律と全単体の実対応
概要：元の native HA 全成分を復元し、Λ からの実 dg 関手との実逆対応を構成する。
方針：任意部分集合を元の昇順列と終点へ分け、全 cell 回収と最高生成元像を使う。
規約：元の全対象・部分集合・次数を保持。使われ方：全単体作用素と tensor 比較の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の任意の native HA 部分集合成分は、実逆 dg 関手から再抽出すると厳密に戻る。 -/
lemma simplexHAInverseFunctor_native_hom {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (I : Finset (Fin (N + 1))) (a b : Fin (N + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ)) :
    (cubicalLambdaNativeSimplex A (simplexHAInverseFunctor A s)).hom I a b k hI ha hb hk =
      s.hom I a b k hI ha hb hk := by
  let m := I.card - 2
  let v := simplexHASubsetPrefixOrder I hI
  have hblast : v (Fin.last m) < b :=
    (simplexHASubsetPrefixOrder_last_lt I hI).trans_eq hb.symm
  have hset : simplexHADecodeSubset m v {b} = I := by
    rw [hb]
    exact simplexHASubsetPrefixOrder_subset I hI
  have hfirst : v 0 = a := (simplexHASubsetPrefixOrder_first I hI).trans ha.symm
  have hdegree : -(m : ℤ) = k := by dsimp [m]; omega
  have hT : ({b} : Finset (Fin (N + 1))).Nonempty := Finset.singleton_nonempty b
  have hbound : ∀ t ∈ ({b} : Finset (Fin (N + 1))), v (Fin.last m) < t :=
    fun _ ht => (Finset.mem_singleton.mp ht) ▸ hblast
  have hDec := simplexHADecodeSubset_two m v {b} hT hbound
  have hmin := (simplexHADecodeSubset_min m v {b} hbound).symm
  have hmax := (simplexHADecodeSubset_max m v {b} hT hbound).symm
  have hdeg : -(m : ℤ) = 2 - ((simplexHADecodeSubset m v {b}).card : ℤ) := by
    rw [hset]
    omega
  let t := cubicalLambdaNativeSimplex A (simplexHAInverseFunctor A s)
  have hN := t.toSimplexData.hom_heq_of_indices_degree
    (hI := hDec) (ha := hmin) (hb := hmax) (hk := hdeg)
      (hJ := hI) (hc := ha) (hd := hb) (hl := hk) hset hfirst rfl hdegree
  have hS := s.toSimplexData.hom_heq_of_indices_degree
    (hI := hDec) (ha := hmin) (hb := hmax) (hk := hdeg)
      (hJ := hI) (hc := ha) (hd := hb) (hl := hk) hset hfirst rfl hdegree
  exact eq_of_heq (hN.symm.trans
    ((heq_of_eq (simplexHAInverseFunctor_native_decoded_hom A s m v b hblast)).trans hS))

/-- 元の native HA 単体を実 dg 関手にして戻すと、元の全単体が厳密に戻る。 -/
lemma cubicalLambdaNativeSimplex_inverse {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    cubicalLambdaNativeSimplex A (simplexHAInverseFunctor A s) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    exact simplexHAInverseFunctor_native_hom A s I a b k hI ha hb hk

/-- 元の Λ 標準単体からの全実 dg 関手と、元の全 native HA 単体の実逆対応。 -/
def cubicalLambdaNativeSimplexEquiv (N : ℕ) :
    DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N where
  toFun := cubicalLambdaNativeSimplex A
  invFun := simplexHAInverseFunctor A
  left_inv := simplexHAInverseFunctor_native A
  right_inv := cubicalLambdaNativeSimplex_inverse A

end SerrePositivity.KST.SConstruction
