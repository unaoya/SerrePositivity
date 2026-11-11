module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeRawValues
public import SerrePositivity.KST.SConstruction.SimplexHADegreeLift
public import SerrePositivity.KST.SConstruction.SimplexHATopValueRecovery

/-! # 元の右端零面と HA 線形復元の制限
概要：元の右端零面へ制限した全次数の線形復元は、同じ最右頂点を削除した復元。
方針：全生成元の零端点読み替えと元の端点挿入の次数移送付き表示で判定する。
規約：元の実零面射と任意の HA データを保持。使われ方：混在生成元の微分条件の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の零端点追加生成元の HA 値は、同じ最右頂点を削除した前段の HA 値。 -/
lemma simplexHAGeneratorValue_point_zero_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 2) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last (m + 1)) < b) :
    HEq (simplexHAGeneratorValue A s (m + 1) (i, 0) v b hb)
      (simplexHAGeneratorValue A s m i (Fin.castSuccOrderEmb.trans v) b
        ((simplexHADecodePrefix_last m v).trans hb)) := by
  exact (complexElement_degree_cast_heq A _
    (serreCubeGeneratorDegree_freeDimension (m + 1) (i, 0)).symm _).trans
      ((heq_of_eq (simplexHABeadWordDecode_zero_rawValue A s m i v {b}
        (Finset.singleton_nonempty b) (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))).trans
          (complexElement_degree_cast_heq A _
            (serreCubeGeneratorDegree_freeDimension m i).symm _).symm)

/-- 元の右端零面への前合成は、全整数次数で元の削除頂点列の HA 線形復元と一致する。 -/
lemma simplexHADegreeLift_zero_face_restriction {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (k : ℤ) :
    (serreCubeFace A false m 0).hom.f k ≫ simplexHADegreeLift A s (m + 1) v b hb k =
      simplexHADegreeLift A s m (Fin.castSuccOrderEmb.trans v) b
        ((simplexHADecodePrefix_last m v).trans hb) k := by
  apply serreCube_degree_hom_ext A m k
  intro i hi
  have hj : serreCubeGeneratorDegree (m + 1) (i, 0) = k := (add_zero _).trans hi
  have h := congrArg (fun w => simplexHADegreeLift A s (m + 1) v b hb k w)
    (serreCubeGenerator_point_cast A false m i k hi)
  have hv : eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X hj)
      (simplexHAGeneratorValue A s (m + 1) (i, 0) v b hb) =
      eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X hi)
        (simplexHAGeneratorValue A s m i (Fin.castSuccOrderEmb.trans v) b
          ((simplexHADecodePrefix_last m v).trans hb)) := by
    exact eq_of_heq ((complexElement_degree_cast_heq A _ hj _).trans
      ((simplexHAGeneratorValue_point_zero_heq A s m i v b hb).trans
        (complexElement_degree_cast_heq A _ hi _).symm))
  exact h.trans ((simplexHADegreeLift_generator A s (m + 1) v b hb k (i, 0) hj).trans
    (hv.trans (simplexHADegreeLift_generator A s m (Fin.castSuccOrderEmb.trans v) b
      ((simplexHADecodePrefix_last m v).trans hb) k i hi).symm))

end SerrePositivity.KST.SConstruction
