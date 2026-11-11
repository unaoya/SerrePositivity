module
public import SerrePositivity.KST.SConstruction.SerreCubeFaceGeneratorImage
public import SerrePositivity.KST.SConstruction.SimplexHACutFaceValue
public import SerrePositivity.KST.SConstruction.SimplexHATopValueRecovery

/-! # 元の HA 線形復元の標準両面最高生成元像
概要：元の標準零面・一面の最高生成元像を、HA 削除成分・切断合成として評価する。
方針：元の面生成元表示と指定値の回収、元の全座標の読み替え値を合成する。
規約：元の次数と向き符号を保持。使われ方：HA 方程式と元の全面微分の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の両標準面の最高生成元像の線形復元は、元の一端点生成元への指定値。 -/
lemma simplexHADegreeLift_face_top_value {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (e : Bool) (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
        ((serreCubeFace A e m i).hom.f (-(m : ℤ)) (serreCubeTopCell A m)) =
      eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
        (serreCubeFaceGeneratorIndex_degree e m i))
          (simplexHAGeneratorValue A s (m + 1) (serreCubeFaceGeneratorIndex e m i) v b hb) :=
  (congrArg (fun w => simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ)) w)
    (serreCubeFace_top_generator A e m i)).trans
      (simplexHADegreeLift_generator A s (m + 1) v b hb _
        (serreCubeFaceGeneratorIndex e m i) (serreCubeFaceGeneratorIndex_degree e m i))

/-- 元の両面の線形復元値は、元の一端点生成元語の生の HA 値を回収する。 -/
lemma simplexHADegreeLift_face_top_word_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (e : Bool) (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    HEq (simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
      ((serreCubeFace A e m i).hom.f (-(m : ℤ)) (serreCubeTopCell A m)))
      (simplexHABeadWordRawValue A s
        (simplexHAGeneratorWord (m + 1) (serreCubeFaceGeneratorIndex e m i) v b hb)) :=
  (heq_of_eq (simplexHADegreeLift_face_top_value A s e m v b hb i)).trans
    ((complexElement_degree_cast_heq A _ (serreCubeFaceGeneratorIndex_degree e m i) _).trans
      (complexElement_degree_cast_heq A _ (serreCubeGeneratorDegree_freeDimension (m + 1)
        (serreCubeFaceGeneratorIndex e m i)).symm _))

private lemma graded_units_smul_heq {x y : D} {p q : ℤ} (hp : p = q)
    (e e' : ℤˣ) (he : e = e') (f : GradedHom A x y p) (g : GradedHom A x y q)
    (hfg : HEq f g) : HEq (e • f) (e' • g) := by
  cases hp
  cases he
  cases eq_of_heq hfg
  rfl

/-- 元の全標準零面像の線形復元値は、同じ内部頂点削除成分の元の向き付き値。 -/
lemma simplexHADegreeLift_zero_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
        ((serreCubeFace A false m i).hom.f (-(m : ℤ)) (serreCubeTopCell A m)) =
      serreCubeOrientationSign m • simplexHADeletedFaceValue A s m v {b}
        (Finset.singleton_nonempty b) (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i := by
  have hd := serreCubeFaceGeneratorIndex_freeDimension false m i
  exact eq_of_heq ((simplexHADegreeLift_face_top_word_heq A s false m v b hb i).trans
    (graded_units_smul_heq A (by
      rw [hd]
      simp only [Finset.card_singleton, Nat.add_sub_cancel]) _ _
        (congrArg serreCubeOrientationSign hd) _ _
      (simplexHABeadWordDecode_face_zero_value A s m v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i)))

/-- 元の全標準一面像の線形復元値は、同じ内部頂点の HA 切断合成の元の向き付き値。 -/
lemma simplexHADegreeLift_one_face_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    HEq (simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
      ((serreCubeFace A true m i).hom.f (-(m : ℤ)) (serreCubeTopCell A m)))
      (serreCubeOrientationSign m • simplexHACutFaceValue A s m v {b}
        (Finset.singleton_nonempty b) (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i) := by
  have hd := serreCubeFaceGeneratorIndex_freeDimension true m i
  exact (simplexHADegreeLift_face_top_word_heq A s true m v b hb i).trans
    (graded_units_smul_heq A (by
      rw [hd]
      simp only [Finset.card_singleton, Nat.cast_add, Nat.cast_one]
      omega) _ _ (congrArg serreCubeOrientationSign hd) _ _
      (simplexHABeadWordDecode_face_one_value A s m v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i))

end SerrePositivity.KST.SConstruction
