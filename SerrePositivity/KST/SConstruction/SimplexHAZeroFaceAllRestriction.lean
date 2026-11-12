module
public import SerrePositivity.KST.SConstruction.SimplexHAInsertZeroValues
public import SerrePositivity.KST.SConstruction.SerreCubeInsertGeneratorImage

/-! # 元の全座標の零面と HA 線形復元の制限
概要：任意位置の元の零面への制限は、同じ内部頂点を削除した線形復元。
方針：全生成元上の実面像と HA 値を比較し、元の始点の等号で Hom 複体を移送する。
規約：元の実面射・全整数次数を保持。使われ方：内部零端点を含む微分条件の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma complex_object_cast_heq (K L : Complex A) (h : K = L) (k : ℤ) (x : K.X k) :
    HEq ((eqToHom h).f k x) x := by
  cases h
  rfl

/-- 元の全座標の零面への制限は、元の始点を保つ同じ削除列の線形復元。 -/
lemma simplexHADegreeLift_zero_face_all_restriction {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (q : Fin (m + 1)) (v : Fin (m + 2) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last (m + 1)) < b) (k : ℤ) :
    (serreCubeFace A false m q).hom.f k ≫ simplexHADegreeLift A s (m + 1) v b hb k =
      simplexHADegreeLift A s m (simplexHADeleteVertexOrder m q v) b
        ((v.monotone (Fin.le_last _)).trans_lt hb) k ≫
          (eqToHom (congrArg (fun a => homObject A D (s.obj a) (s.obj b))
            (simplexHADeleteVertexOrder_first m q v))).f k := by
  let w := simplexHADeleteVertexOrder m q v
  let hw := (v.monotone
    (Fin.le_last ((simplexHAFaceVertex m q).succAbove (Fin.last m)))).trans_lt hb
  let E : homObject A D (s.obj (w 0)) (s.obj b) ⟶ homObject A D (s.obj (v 0)) (s.obj b) :=
    eqToHom (congrArg (fun a => homObject A D (s.obj a) (s.obj b))
      (simplexHADeleteVertexOrder_first m q v))
  apply serreCube_degree_hom_ext A m k
  intro i hi
  let j := serreCubeInsertGeneratorIndex false m q i
  have hj : serreCubeGeneratorDegree (m + 1) j = k :=
    (serreCubeInsertGeneratorIndex_degree false m q i).trans hi
  have h := congrArg (fun x => simplexHADegreeLift A s (m + 1) v b hb k x)
    (serreCubeFace_generator_cast A false m q i k hi)
  have hv : eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X hj)
      (simplexHAGeneratorValue A s (m + 1) j v b hb) =
      E.f k (eqToHom (congrArg (homObject A D (s.obj (w 0)) (s.obj b)).X hi)
        (simplexHAGeneratorValue A s m i w b hw)) := by
    exact eq_of_heq ((complexElement_degree_cast_heq A _ hj _).trans
      ((simplexHAGeneratorValue_insert_zero_heq A s m q i v b hb).trans
        ((complexElement_degree_cast_heq A _ hi _).symm.trans
          (complex_object_cast_heq A _ _ _ k _).symm)))
  have ht := congrArg (fun x => E.f k x)
    (simplexHADegreeLift_generator A s m w b hw k i hi)
  exact h.trans ((simplexHADegreeLift_generator A s (m + 1) v b hb k j hj).trans
    (hv.trans ht.symm))

end SerrePositivity.KST.SConstruction
