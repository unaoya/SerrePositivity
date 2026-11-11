module
public import SerrePositivity.KST.SConstruction.SimplexHAOrientedFaceValues
public import SerrePositivity.KST.SConstruction.SimplexHAFaceRhsSum

/-! # 元の HA 方程式の共通出力次数の両面像
概要：元の HA 向き標準両面像を、元の方程式の出力次数へ移して比較する。
方針：元の次数等号による移送と両面評価を、元の削除・切断成分へ接続する。
規約：元の実面射と HA 右辺の次数を保持。使われ方：最高生成元の微分可換性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の右側一点の部分集合成分の次数は、元の全自由座標次元の負値。 -/
lemma simplexHADecodeSingleton_degree {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) :
    -((m + 1 : ℕ) : ℤ) = 2 - ((simplexHADecodeSubset (m + 1) v {b}).card : ℤ) := by
  have h := simplexHADecodeSubset_card (m + 1) v {b}
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
  simp only [Finset.card_singleton] at h
  omega

/-- 元の次数移送は、元の異種等号で比較した同じ斉次元を回収する。 -/
lemma complexElement_degree_cast_eq (K : Complex A) {p q : ℤ} (h : p = q)
    (x : K.X p) (y : K.X q) (hxy : HEq x y) :
    eqToHom (congrArg K.X h) x = y := by
  cases h
  exact eq_of_heq hxy

/-- 元の HA 方程式と同じ出力次数に置いた、元の内部頂点削除成分。 -/
def simplexHAErasedFaceComponent {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    GradedHom A (s.obj (v 0)) (s.obj b) (-((m + 1 : ℕ) : ℤ) + 1) :=
  s.erasedComponent (simplexHADecodeSubset (m + 1) v {b}) (v 0) b _
    (simplexHADecodeSubset_two (m + 1) v {b} (Finset.singleton_nonempty b)
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
    (simplexHADecodeSubset_min (m + 1) v {b}
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm
    (simplexHADecodeSubset_max (m + 1) v {b} (Finset.singleton_nonempty b)
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm
    (simplexHADecodeSingleton_degree m v b hb) (v (simplexHAFaceVertex m i))
    (simplexHAFaceVertex_mem m v {b} i) (simplexHAFaceVertex_first_lt m v i)
    (simplexHAFaceVertex_tail_lt m v {b} i
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) b (Finset.mem_singleton_self b))

/-- 元の HA 向き標準面像を、元の HA 方程式の同じ出力次数へ移す。 -/
def simplexHAOrientedFaceImage {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (e : Bool) (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    GradedHom A (s.obj (v 0)) (s.obj b) (-((m + 1 : ℕ) : ℤ) + 1) :=
  eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X
    (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega))
      (simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
        ((serreCubeFace A e m i).hom.f (-(m : ℤ)) (serreCubeOrientedTopCell A m)))

/-- 元の削除成分は、元の HA 方程式の出力次数で同じ元と異種等号で一致する。 -/
lemma simplexHADeletedFaceValue_component_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    HEq (simplexHADeletedFaceValue A s m v {b} (Finset.singleton_nonempty b)
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i)
      (simplexHAErasedFaceComponent A s m v b hb i) :=
  s.hom_heq_of_indices_degree rfl rfl rfl (by
    simp only [Finset.card_singleton, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    omega)

/-- 元の共通 HA 出力次数の零面像は、元の同じ内部頂点削除成分。 -/
lemma simplexHAOrientedFaceImage_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    simplexHAOrientedFaceImage A s false m v b hb i =
      simplexHAErasedFaceComponent A s m v b hb i :=
  complexElement_degree_cast_eq A _ (by omega) _ _
    ((heq_of_eq (simplexHADegreeLift_oriented_zero_face A s m v b hb i)).trans
      (simplexHADeletedFaceValue_component_heq A s m v b hb i))

/-- 元の共通 HA 出力次数の一面像は、元の同じ内部頂点の HA 切断合成。 -/
lemma simplexHAOrientedFaceImage_one {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    simplexHAOrientedFaceImage A s true m v b hb i =
      simplexHACutFaceValue A s m v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i :=
  complexElement_degree_cast_eq A _ (by omega) _ _
    (simplexHADegreeLift_oriented_one_face_heq A s m v b hb i)

end SerrePositivity.KST.SConstruction
