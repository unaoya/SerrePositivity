module
public import SerrePositivity.KST.SConstruction.SimplexHADeleteVertexSubset
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCell
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaSpecifiedFace

/-! # 元の全零面における HA 部分集合生成射の削除
概要：元の任意座標の零面への実部分集合生成射の制限は、同じ面頂点を削除した生成射。
方針：元の削除集合・濃度・右端座標を、指定次元の実零面公式へ照合する。
規約：元の実鎖面・全頂点・両端を保持。使われ方：任意部分集合上の HA 逆律。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の任意座標の零面は、同じ面頂点を削除した部分集合の実生成射を回収する。 -/
lemma simplexHADecodeSubsetCell_delete_zero_face_heq {N : ℕ} (m : ℕ) (q : Fin (m + 1))
    (v : Fin (m + 2) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (m + 1)) < b) :
    HEq ((serreCubeFace A false m q).hom ≫
      simplexHADecodeSubsetCell A (m + 1) v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
      (simplexHADecodeSubsetCell A m (simplexHADeleteVertexOrder m q v) {b}
        (Finset.singleton_nonempty b) (simplexHADeleteVertexOrder_bound m q v {b}
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))) := by
  let I := simplexHADecodeSubset (m + 1) v {b}
  let r := v (simplexHAFaceVertex m q)
  have hT : ({b} : Finset (Fin (N + 1))).Nonempty := Finset.singleton_nonempty b
  have hbound : ∀ t ∈ ({b} : Finset (Fin (N + 1))), v (Fin.last (m + 1)) < t :=
    fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb
  have hI : 2 ≤ I.card := simplexHADecodeSubset_two (m + 1) v {b} hT hbound
  have hr : r ∈ I := simplexHAFaceVertex_mem m v {b} q
  have hmin : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < r := by
    rw [simplexHADecodeSubset_min (m + 1) v {b} hbound]
    exact simplexHAFaceVertex_first_lt m v q
  have hmax : r < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) := by
    rw [simplexHADecodeSubset_max (m + 1) v {b} hT hbound]
    exact simplexHAFaceVertex_tail_lt m v {b} q hbound b (Finset.mem_singleton_self b)
  have he := simplexHADeleteVertexOrder_subset m q v {b} hbound
  have hd := simplexHADeleteVertexOrder_bound m q v {b} hbound
  have hD := simplexHADecodeSubset_two m (simplexHADeleteVertexOrder m q v) {b} hT hd
  have hp : m = (I.erase r).card - 2 := by
    rw [← he, simplexHADecodeSubset_card m (simplexHADeleteVertexOrder m q v) {b} hd,
      Finset.card_singleton]
    omega
  have hq : m + 1 = I.card - 2 := by
    rw [simplexHADecodeSubset_card (m + 1) v {b} hbound, Finset.card_singleton]
    omega
  have hi : Fin.cast hq.symm (simplexSubsetEraseNormalizedCoordinate I hI r hr hmin hmax) = q :=
    Fin.ext (simplexHADeleteVertexOrder_coordinate m q v b hb hI)
  have hz := simplexSubsetLambdaCellAtDimension_zero_face_at A I hI r hr hmin hmax
    (v 0) b (simplexHADecodeSubset_min (m + 1) v {b} hbound).symm
    (simplexHADecodeSubset_max (m + 1) v {b} hT hbound).symm m (m + 1) hp hq rfl
  rw [hi, serreCubeChainFace_refl] at hz
  have h₀ := simplexSubsetLambdaCellAtDimension_canonical_heq A (I.erase r) (v 0) b
    (simplexSubsetErase_two I hI r hmin hmax)
    ((simplexHADecodeSubset_min (m + 1) v {b} hbound).symm.trans
      (simplexSubsetErase_min I hI r hmin hmax).symm)
    ((simplexHADecodeSubset_max (m + 1) v {b} hT hbound).symm.trans
      (simplexSubsetErase_max I hI r hmin hmax).symm) m hp
  have h₁ := simplexSubsetLambdaCell_heq_of_eq A _ _ he.symm
    (simplexSubsetErase_two I hI r hmin hmax) hD
  have h₂ := simplexHADecodeSubsetCell_canonical_heq A m
    (simplexHADeleteVertexOrder m q v) {b} hT hd
  exact (heq_of_eq hz).trans (h₀.trans (h₁.trans h₂.symm))

end SerrePositivity.KST.SConstruction
