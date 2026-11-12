module
public import SerrePositivity.KST.SConstruction.SimplexHAFaceInteriorEquiv
public import SerrePositivity.KST.SConstruction.SimplexSubsetInteriorSum

/-! # 元の HA 右辺の読み替え面座標和
概要：元の頂点集合の全内部頂点和を、元の全標準面座標による同じ寄与の和へ移す。
方針：元の内部頂点和と面頂点同値の有限和を、同じ指定端点・次数で合成する。
規約：元の HA 項と所属証明を保持。使われ方：任意 HA 単体の全面像和との比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped BigOperators
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の指定端点・次数の HA 右辺は、同じ所属内部頂点の元の項の和。 -/
lemma simplexHARhs_interior {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    s.rhs I a b k hI ha hb hk =
      ∑ j : SimplexSubsetInterior I hI, s.term I a b k hI ha hb hk j.val j.property.1
        (ha.trans_lt j.property.2.1) (j.property.2.2.trans_eq hb.symm) := by
  subst a b
  exact simplexSubset_sum_interior I hI (fun j hj haj hjb =>
    s.term I _ _ k hI rfl rfl hk j hj haj hjb)

/-- 元の読み替え部分集合の HA 右辺は、同じ元の全ての面座標の寄与の和。 -/
lemma simplexHADecode_rhs_faces {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (k : ℤ)
    (hk : k = 2 - ((simplexHADecodeSubset (m + 1) v {b}).card : ℤ)) :
    let htail : ∀ t ∈ ({b} : Finset (Fin (n + 1))), v (Fin.last (m + 1)) < t :=
      fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb
    let I := simplexHADecodeSubset (m + 1) v {b}
    let hI := simplexHADecodeSubset_two (m + 1) v {b} (Finset.singleton_nonempty b) htail
    let ha := (simplexHADecodeSubset_min (m + 1) v {b} htail).symm
    let hM := (simplexHADecodeSubset_max (m + 1) v {b} (Finset.singleton_nonempty b) htail).symm
    s.rhs I (v 0) b k hI ha hM hk = ∑ i : Fin (m + 1),
      s.term I (v 0) b k hI ha hM hk (v (simplexHAFaceVertex m i))
        (simplexHAFaceVertex_mem m v {b} i) (simplexHAFaceVertex_first_lt m v i)
        (simplexHAFaceVertex_tail_lt m v {b} i htail b (Finset.mem_singleton_self b)) := by
  dsimp only
  let htail : ∀ t ∈ ({b} : Finset (Fin (n + 1))), v (Fin.last (m + 1)) < t :=
    fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb
  let I := simplexHADecodeSubset (m + 1) v {b}
  have hI := simplexHADecodeSubset_two (m + 1) v {b} (Finset.singleton_nonempty b) htail
  have ha := (simplexHADecodeSubset_min (m + 1) v {b} htail).symm
  have hM := (simplexHADecodeSubset_max (m + 1) v {b} (Finset.singleton_nonempty b) htail).symm
  have he := (simplexHAFaceInteriorEquiv m v b hb).sum_comp
    (fun j => s.term I (v 0) b k hI ha hM hk j.val j.property.1
      (ha.trans_lt j.property.2.1) (j.property.2.2.trans_eq hM.symm))
  exact (simplexHARhs_interior A s I (v 0) b k hI ha hM hk).trans he.symm

end SerrePositivity.KST.SConstruction
