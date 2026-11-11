module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeInsertZero
public import SerrePositivity.KST.SConstruction.SimplexHARightTailValues
public import SerrePositivity.KST.SConstruction.SimplexHAZeroFaceRestriction

/-! # 元の任意位置の零端点挿入生成元の HA 値
概要：元の任意位置へ零端点を挿入した生成元の値を、同じ削除列の値へ戻す。
方針：元の両端点・自由次元と読み替え語の一致を、生の値と生成元次数へ移す。
規約：任意の HA データを保持。使われ方：全座標の零面への次数線形復元の制限。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の全座標への零端点挿入生成元の HA 値は、同じ内部頂点を削除した値。 -/
lemma simplexHAGeneratorValue_insert_zero_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (q : Fin (m + 1)) (i : SerreCubeGeneratorIndex m)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) :
    HEq (simplexHAGeneratorValue A s (m + 1) (serreCubeInsertGeneratorIndex false m q i) v b hb)
      (simplexHAGeneratorValue A s m i (simplexHADeleteVertexOrder m q v) b
        ((v.monotone (Fin.le_last _)).trans_lt hb)) := by
  let w := simplexHADeleteVertexOrder m q v
  have hw := simplexHABeadWordDecode_insert_zero m q i v {b} (Finset.singleton_nonempty b)
    (fun _ hr => (Finset.mem_singleton.mp hr) ▸ hb)
  have hv := simplexHABeadWordRawValue_heq A s
    (simplexHADeleteVertexOrder_first m q v).symm rfl
    (serreCubeInsertGeneratorIndex_freeDimension false m q i) _ _ hw
  exact (complexElement_degree_cast_heq A _
    (serreCubeGeneratorDegree_freeDimension (m + 1)
      (serreCubeInsertGeneratorIndex false m q i)).symm _).trans
      (hv.trans (complexElement_degree_cast_heq A _
        (serreCubeGeneratorDegree_freeDimension m i).symm _).symm)

end SerrePositivity.KST.SConstruction
