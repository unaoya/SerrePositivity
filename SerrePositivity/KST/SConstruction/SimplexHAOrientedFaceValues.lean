module
public import SerrePositivity.KST.SConstruction.SimplexHADegreeFaceValues
public import SerrePositivity.KST.SConstruction.SerreCubeOrientedTopCell

/-! # 元の HA 向き標準両面の線形復元値
概要：元の標準面に HA 向き最高生成元を入れると、向き補正のない HA 成分を回収する。
方針：元の両線形射の整数単元作用と、二回の同じ向き補正の消去を使う。
規約：元の実面射・HA 向き生成元を保持。使われ方：元の HA 右辺と全面微分の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma units_smul_map (V W : ModuleCat.{u} A) (f : V ⟶ W) (e : ℤˣ) (x : V) :
    f (e • x) = e • f x := by
  simp only [Units.smul_def, map_zsmul]

private lemma units_smul_cancel (M : Type u) [AddCommGroup M] (e : ℤˣ) (x : M) :
    e • (e • x) = x := by
  rw [smul_smul, Int.units_mul_self, one_smul]

private lemma units_smul_heq (K : Complex A) {p q : ℤ} (h : p = q)
    (e : ℤˣ) (x : K.X p) (y : K.X q) (hxy : HEq x y) : HEq (e • x) (e • y) := by
  cases h
  cases eq_of_heq hxy
  rfl

/-- 元の HA 向き両面像は、元の生の両面像の線形復元値の同じ向き補正。 -/
lemma simplexHADegreeLift_oriented_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (e : Bool) (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
        ((serreCubeFace A e m i).hom.f (-(m : ℤ)) (serreCubeOrientedTopCell A m)) =
      serreCubeOrientationSign m • simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
        ((serreCubeFace A e m i).hom.f (-(m : ℤ)) (serreCubeTopCell A m)) :=
  units_smul_map A _ _ ((serreCubeFace A e m i).hom.f (-(m : ℤ)) ≫
    simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))) _ _

/-- 元の HA 向き零面像の線形復元値は、元の同じ内部頂点削除成分。 -/
lemma simplexHADegreeLift_oriented_zero_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
        ((serreCubeFace A false m i).hom.f (-(m : ℤ)) (serreCubeOrientedTopCell A m)) =
      simplexHADeletedFaceValue A s m v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i :=
  (simplexHADegreeLift_oriented_face A s false m v b hb i).trans
    ((congrArg (fun w => serreCubeOrientationSign m • w)
      (simplexHADegreeLift_zero_face A s m v b hb i)).trans (units_smul_cancel _ _ _))

/-- 元の HA 向き一面像の線形復元値は、元の同じ内部頂点の HA 切断合成。 -/
lemma simplexHADegreeLift_oriented_one_face_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    HEq (simplexHADegreeLift A s (m + 1) v b hb (-(m : ℤ))
      ((serreCubeFace A true m i).hom.f (-(m : ℤ)) (serreCubeOrientedTopCell A m)))
      (simplexHACutFaceValue A s m v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i) :=
  (heq_of_eq (simplexHADegreeLift_oriented_face A s true m v b hb i)).trans
    ((units_smul_heq A _ (by simp only [Finset.card_singleton, Nat.cast_add, Nat.cast_one]; omega)
      (serreCubeOrientationSign m) _ _ (simplexHADegreeLift_one_face_heq A s m v b hb i)).trans
        (heq_of_eq (units_smul_cancel _ _ _)))

end SerrePositivity.KST.SConstruction
