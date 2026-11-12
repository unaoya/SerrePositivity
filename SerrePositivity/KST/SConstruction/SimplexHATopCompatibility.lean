module
public import SerrePositivity.KST.SConstruction.SimplexHAOrientedRhsFaces
public import SerrePositivity.KST.SConstruction.SimplexHATopDifferential
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImageDifferentialTransport

/-! # 元の HA 線形復元の最高生成元上の微分可換性
概要：任意の native HA 単体の線形復元は、元の全正次元の最高生成元上で微分と可換。
方針：HA 向き最高生成元の方程式と元の全面微分を同じ次数・同じ両面像和で比較する。
規約：元の実微分・生成元を保持。使われ方：全生成元上の微分可換性と逆 Hom 鎖射。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped BigOperators
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の同じ次数移送後の元が一致すれば、元の同じ加群の元も一致する。 -/
lemma complexElement_degree_cast_injective (K : Complex A) {p q : ℤ} (h : p = q) :
    Function.Injective (fun x : K.X p => eqToHom (congrArg K.X h) x) := by
  cases h
  intro x y hxy
  exact hxy

private lemma units_smul_map (V W : ModuleCat.{u} A) (f : V ⟶ W) (e : ℤˣ) (x : V) :
    f (e • x) = e • f x := by
  simp only [Units.smul_def, map_zsmul]

private lemma units_smul_cancel (M : Type u) [AddCommGroup M] (e : ℤˣ) (x : M) :
    e • (e • x) = x := by
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- 元の全正次元の HA 向き最高生成元上で、元の HA 線形復元は微分と可換。 -/
lemma simplexHADegreeLift_oriented_top_comm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) :
    (homObject A D (s.obj (v 0)) (s.obj b)).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))
        (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (-((m + 1 : ℕ) : ℤ))
          (serreCubeOrientedTopCell A (m + 1))) =
      simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (-(m : ℤ))
        ((serreCubeComplex A (m + 1)).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))
          (serreCubeOrientedTopCell A (m + 1))) := by
  let htail : ∀ t ∈ ({b} : Finset (Fin (n + 1))), v (Fin.last (m + 1)) < t :=
    fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb
  let I := simplexHADecodeSubset (m + 1) v {b}
  let K := homObject A D (s.obj (v 0)) (s.obj b)
  let a : ℤ := -((m + 1 : ℕ) : ℤ)
  have hc : -(m : ℤ) = a + 1 := by dsimp only [a]; omega
  have hI := simplexHADecodeSubset_two (m + 1) v {b} (Finset.singleton_nonempty b) htail
  have ha := (simplexHADecodeSubset_min (m + 1) v {b} htail).symm
  have hM := (simplexHADecodeSubset_max (m + 1) v {b} (Finset.singleton_nonempty b) htail).symm
  have hk := simplexHADecodeSingleton_degree m v b hb
  let L := simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (-(m : ℤ))
  let F := L ≫ eqToHom (congrArg K.X hc)
  have ht : simplexHADegreeLift A s.toSimplexData (m + 1) v b hb a
      (serreCubeOrientedTopCell A (m + 1)) = s.hom I (v 0) b a hI ha hM hk :=
    (units_smul_map A _ _ (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb a)
      (serreCubeOrientationSign (m + 1)) (serreCubeTopCell A (m + 1))).trans
      ((congrArg (fun w => serreCubeOrientationSign (m + 1) • w)
        (simplexHADegreeLift_top A s.toSimplexData (m + 1) v b hb)).trans
          (units_smul_cancel _ _ _))
  have hd : K.d a (a + 1) (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb a
      (serreCubeOrientedTopCell A (m + 1))) = s.toSimplexData.rhs I (v 0) b a hI ha hM hk :=
    (congrArg (differential A) ht).trans (s.equation I (v 0) b a hI ha hM hk)
  have hB : F ((serreCubeComplex A (m + 1)).d a (-(m : ℤ))
      (serreCubeOrientedTopCell A (m + 1))) =
      ∑ i : Fin (m + 1), ((i.val : ℤ) + 1).negOnePow •
        (simplexHAOrientedFaceImage A s.toSimplexData false m v b hb i -
          simplexHAOrientedFaceImage A s.toSimplexData true m v b hb i) := by
    have hlin : F (∑ i : Fin (m + 1), ((i.val : ℤ) + 1).negOnePow •
        ((serreCubeFace A false m i).hom.f (-(m : ℤ)) (serreCubeOrientedTopCell A m) -
          (serreCubeFace A true m i).hom.f (-(m : ℤ)) (serreCubeOrientedTopCell A m))) =
        ∑ i : Fin (m + 1), ((i.val : ℤ) + 1).negOnePow •
          (F ((serreCubeFace A false m i).hom.f (-(m : ℤ)) (serreCubeOrientedTopCell A m)) -
            F ((serreCubeFace A true m i).hom.f (-(m : ℤ)) (serreCubeOrientedTopCell A m))) := by
      simp only [map_sum, Units.smul_def, map_zsmul, map_sub]
    exact (congrArg (fun w => F w) (serreCubeOrientedTopCell_d A m)).trans hlin
  have hdc : K.d a (a + 1) (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb a
      (serreCubeOrientedTopCell A (m + 1))) =
      eqToHom (congrArg K.X hc)
        (K.d a (-(m : ℤ)) (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb a
          (serreCubeOrientedTopCell A (m + 1)))) :=
    complexDifferential_degree_transport A K rfl hc _
  apply complexElement_degree_cast_injective A K hc
  exact hdc.symm.trans (hd.trans
    ((simplexHADecode_rhs_oriented_faces A s.toSimplexData m v b hb hI ha hM hk).trans hB.symm))

/-- 元の全正次元の生の最高生成元上で、元の HA 線形復元は微分と可換。 -/
lemma simplexHADegreeLift_top_comm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) :
    (homObject A D (s.obj (v 0)) (s.obj b)).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))
        (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (-((m + 1 : ℕ) : ℤ))
          (serreCubeTopCell A (m + 1))) =
      simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (-(m : ℤ))
        ((serreCubeComplex A (m + 1)).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))
          (serreCubeTopCell A (m + 1))) := by
  let f := simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (-((m + 1 : ℕ) : ℤ)) ≫
    (homObject A D (s.obj (v 0)) (s.obj b)).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))
  let g := (serreCubeComplex A (m + 1)).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ)) ≫
    simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (-(m : ℤ))
  have h := simplexHADegreeLift_oriented_top_comm A s m v b hb
  have he := (units_smul_map A _ _ f (serreCubeOrientationSign (m + 1))
    (serreCubeTopCell A (m + 1))).symm.trans
      (h.trans (units_smul_map A _ _ g (serreCubeOrientationSign (m + 1))
        (serreCubeTopCell A (m + 1))))
  exact smul_left_cancel (serreCubeOrientationSign (m + 1)) he

end SerrePositivity.KST.SConstruction
