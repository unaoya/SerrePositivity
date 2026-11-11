module
public import SerrePositivity.KST.SConstruction.SimplexHAChainLift

/-! # 元の実 HA Hom 鎖射の全座標の面制限
概要：全零面は元の削除列へ、内部一面は元の左右の実復元鎖射の tensor 合成へ戻る。
方針：元の全次数の面制限に、構成済みの無条件の左右復元鎖射を供給する。
規約：元の実面・共有端点を保持。使われ方：逆 dg 関手の合成保存と単体作用素比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の全座標の零面への実復元鎖射の制限は、同じ削除列の実復元と始点移送。 -/
lemma simplexHAChainLift_zero_face {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (q : Fin (m + 1)) (v : Fin (m + 2) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (m + 1)) < b) :
    (serreCubeFace A false m q).hom ≫ simplexHAChainLift A s (m + 1) v b hb =
      simplexHAChainLift A s m (simplexHADeleteVertexOrder m q v) b
        ((v.monotone (Fin.le_last _)).trans_lt hb) ≫
          eqToHom (congrArg (fun a => homObject A D (s.obj a) (s.obj b))
            (simplexHADeleteVertexOrder_first m q v)) := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact simplexHADegreeLift_zero_face_all_restriction A s.toSimplexData m q v b hb k

/-- 元の内部一面への実復元鎖射の制限は、同じ左右の実復元鎖射の実 tensor 合成。 -/
lemma simplexHAChainLift_one_tensor {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (n m : ℕ)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (n + 1 + m)) < b) :
    (serreCubeRightFace A true n m).hom ≫ simplexHAChainLift A s (n + 1 + m) v b hb =
      serreCubeTensorComposition A n m
        (simplexHAChainLift A s n (simplexHASplitLeft n m v)
          (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v))
        (simplexHAChainLift A s m (simplexHASplitRight n m v) b
          (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb)) := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact simplexHADegreeLift_one_tensor_restriction A s.toSimplexData n m v b hb
    (simplexHAChainLift A s n (simplexHASplitLeft n m v)
      (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v))
    (simplexHAChainLift A s m (simplexHASplitRight n m v) b
      (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb)) (fun _ => rfl) (fun _ => rfl) k

end SerrePositivity.KST.SConstruction
