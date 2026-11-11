module
public import SerrePositivity.KST.SConstruction.SimplexHASingletonFaceComponents

/-! # 元の HA 右辺と同次数の HA 向き両面像和
概要：元の HA 右辺の各項と全体を、同じ出力次数の元の零面像−一面像へ戻す。
方針：元の削除・切断分解、右側頂点数の符号と両面評価をそのまま合成する。
規約：任意の HA データ・元の全面座標を保持。使われ方：最高生成元の微分比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped BigOperators
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の指定端点・次数の HA 項は、同じ次数の元の HA 向き零面像−一面像の符号倍。 -/
lemma simplexHADecode_term_oriented_faces {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1))
    (hI : 2 ≤ (simplexHADecodeSubset (m + 1) v {b}).card)
    (ha : v 0 = (simplexHADecodeSubset (m + 1) v {b}).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hM : b = (simplexHADecodeSubset (m + 1) v {b}).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : -((m + 1 : ℕ) : ℤ) = 2 - ((simplexHADecodeSubset (m + 1) v {b}).card : ℤ)) :
    s.term (simplexHADecodeSubset (m + 1) v {b}) (v 0) b (-((m + 1 : ℕ) : ℤ)) hI ha hM hk
        (v (simplexHAFaceVertex m i)) (simplexHAFaceVertex_mem m v {b} i)
        (simplexHAFaceVertex_first_lt m v i) (simplexHAFaceVertex_tail_lt m v {b} i
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) b (Finset.mem_singleton_self b)) =
      ((i.val : ℤ) + 1).negOnePow •
        (simplexHAOrientedFaceImage A s false m v b hb i -
          simplexHAOrientedFaceImage A s true m v b hb i) := by
  have ht := s.term_eq_sub_cutComposite (simplexHADecodeSubset (m + 1) v {b}) (v 0) b
    (-((m + 1 : ℕ) : ℤ)) hI ha hM hk (v (simplexHAFaceVertex m i))
    (simplexHAFaceVertex_mem m v {b} i) (simplexHAFaceVertex_first_lt m v i)
    (simplexHAFaceVertex_tail_lt m v {b} i
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) b (Finset.mem_singleton_self b))
  let cut : GradedHom A (s.obj (v 0)) (s.obj b) (-((m + 1 : ℕ) : ℤ) + 1) :=
    simplexHACutFaceValue A s m v {b} (Finset.singleton_nonempty b)
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i
  have hOne : simplexHAOrientedFaceImage A s true m v b hb i = cut :=
    simplexHAOrientedFaceImage_one A s m v b hb i
  have hs := congrArg (fun e => e •
    (simplexHAErasedFaceComponent A s m v b hb i - cut))
    (simplexHAFaceVertex_sign m v b hb i)
  exact ht.trans (hs.trans (congrArg₂ (fun x y => ((i.val : ℤ) + 1).negOnePow • (x - y))
    (simplexHAOrientedFaceImage_zero A s m v b hb i).symm
    hOne.symm))

/-- 元の指定端点・次数の HA 右辺は、元の全ての HA 向き零面像−一面像の符号付き和。 -/
lemma simplexHADecode_rhs_oriented_faces {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b)
    (hI : 2 ≤ (simplexHADecodeSubset (m + 1) v {b}).card)
    (ha : v 0 = (simplexHADecodeSubset (m + 1) v {b}).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hM : b = (simplexHADecodeSubset (m + 1) v {b}).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : -((m + 1 : ℕ) : ℤ) = 2 - ((simplexHADecodeSubset (m + 1) v {b}).card : ℤ)) :
    s.rhs (simplexHADecodeSubset (m + 1) v {b}) (v 0) b
        (-((m + 1 : ℕ) : ℤ)) hI ha hM hk =
      ∑ i : Fin (m + 1), ((i.val : ℤ) + 1).negOnePow •
        (simplexHAOrientedFaceImage A s false m v b hb i -
          simplexHAOrientedFaceImage A s true m v b hb i) :=
  (simplexHADecode_rhs_faces A s m v b hb (-((m + 1 : ℕ) : ℤ)) hk).trans
    (Finset.sum_congr rfl (fun i _ =>
      simplexHADecode_term_oriented_faces A s m v b hb i hI ha hM hk))

end SerrePositivity.KST.SConstruction
