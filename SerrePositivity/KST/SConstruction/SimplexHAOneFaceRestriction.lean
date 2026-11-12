module
public import SerrePositivity.KST.SConstruction.SimplexHAOneFaceValues

/-! # 元の右端一面と閉零辺による HA 線形復元の制限
概要：元の右端一面へ制限した全次数の線形復元を、前段と元の閉零辺の右合成で回収。
方針：元の一端点生成元と全生成元値の回収を、実右合成鎖射の次数移送で比較する。
規約：元の一面射と実鎖射を保持。使われ方：一端点追加生成元の微分条件の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の右端一面への前合成は、全整数次数で前段の復元と元の閉零辺との実右合成。 -/
lemma simplexHADegreeLift_one_face_restriction {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (k : ℤ) :
    (serreCubeFace A true m 0).hom.f k ≫
        simplexHADegreeLift A s.toSimplexData (m + 1) v b hb k =
      simplexHADegreeLift A s.toSimplexData m (Fin.castSuccOrderEmb.trans v)
        (v (Fin.last (m + 1))) (simplexHADecodePrefix_last m v) k ≫
        (dgRightCycleComposition A (x := s.obj (v 0))
          (s.edgeCycle (v (Fin.last (m + 1))) b hb)).f k := by
  apply serreCube_degree_hom_ext A m k
  intro i hi
  let r := v (Fin.last (m + 1))
  let R := dgRightCycleComposition A (x := s.obj (v 0)) (s.edgeCycle r b hb)
  have hj : serreCubeGeneratorDegree (m + 1) (i, 1) = k := (add_zero _).trans hi
  have h := congrArg (fun w => simplexHADegreeLift A s.toSimplexData (m + 1) v b hb k w)
    (serreCubeGenerator_point_cast A true m i k hi)
  have hv : eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X hj)
      (simplexHAGeneratorValue A s.toSimplexData (m + 1) (i, 1) v b hb) =
      eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X hi)
        (R.f (serreCubeGeneratorDegree m i)
          (simplexHAGeneratorValue A s.toSimplexData m i (Fin.castSuccOrderEmb.trans v) r
            (simplexHADecodePrefix_last m v))) := by
    exact eq_of_heq ((complexElement_degree_cast_heq A _ hj _).trans
      ((simplexHAGeneratorValue_point_one_heq A s m i v b hb).trans
        (complexElement_degree_cast_heq A _ hi _).symm))
  have ht := congrArg (fun w => R.f k w)
    (simplexHADegreeLift_generator A s.toSimplexData m (Fin.castSuccOrderEmb.trans v) r
      (simplexHADecodePrefix_last m v) k i hi)
  have hm := complexMap_degree_cast A R hi (simplexHAGeneratorValue A s.toSimplexData m i
    (Fin.castSuccOrderEmb.trans v) r (simplexHADecodePrefix_last m v))
  exact h.trans ((simplexHADegreeLift_generator A s.toSimplexData (m + 1) v b hb k (i, 1) hj).trans
    (hv.trans (ht.trans hm).symm))

end SerrePositivity.KST.SConstruction
