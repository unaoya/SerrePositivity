module
public import SerrePositivity.KST.SConstruction.SimplexHATopDecodeValue
public import SerrePositivity.KST.SConstruction.SimplexHADegreeNaturality

/-! # 元の HA 次数線形復元の最高生成元値
概要：任意の HA 成分データの線形復元から、元の同じ部分集合成分を回収する。
方針：元の全辺添字と最高生成元を比較し、全辺読み替えの成分評価を次数移送する。
規約：元の HA 向き符号を明示する。使われ方：逆構成の右逆と微分可換性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の次数移送を施した斉次元は、同じ元と異種等号で一致する。 -/
lemma complexElement_degree_cast_heq (K : Complex A) {p q : ℤ} (h : p = q) (x : K.X p) :
    HEq (eqToHom (congrArg K.X h) x) x := by
  cases h
  rfl

private lemma orientation_smul_heq {x y : D} {p q : ℕ} (hp : p = q)
    (f : GradedHom A x y (-(p : ℤ))) (g : GradedHom A x y (-(q : ℤ))) (hfg : HEq f g) :
    HEq (serreCubeOrientationSign p • f) (serreCubeOrientationSign q • g) := by
  cases hp
  cases eq_of_heq hfg
  rfl

/-- 元の全辺添字の HA 値は、元の同じ部分集合成分の向きを戻した値。 -/
lemma simplexHAGeneratorValue_top_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) :
    HEq (simplexHAGeneratorValue A s m (serreCubeTopGeneratorIndex m) v b hb)
      (serreCubeOrientationSign m •
        s.hom (simplexHADecodeSubset m v {b}) (v 0) b (-(m : ℤ))
          (simplexHADecodeSubset_two m v {b} (Finset.singleton_nonempty b)
            (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
          (simplexHADecodeSubset_min m v {b}
            (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm
          (simplexHADecodeSubset_max m v {b} (Finset.singleton_nonempty b)
            (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm (by
              have hc := simplexHADecodeSubset_card m v {b}
                (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
              simp only [Finset.card_singleton] at hc
              omega)) := by
  have h := simplexHABeadWordDecode_top_value A s m v {b} (Finset.singleton_nonempty b)
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
  exact (complexElement_degree_cast_heq A _
    (serreCubeGeneratorDegree_freeDimension m (serreCubeTopGeneratorIndex m)).symm _).trans
      (orientation_smul_heq A (serreCubeTopGeneratorIndex_freeDimension m) _ _ h)

/-- 任意の元の HA 次数線形復元は、最高生成元で元の同じ部分集合成分を回収する。 -/
lemma simplexHADegreeLift_top {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) :
    simplexHADegreeLift A s m v b hb (-(m : ℤ)) (serreCubeTopCell A m) =
      serreCubeOrientationSign m •
        s.hom (simplexHADecodeSubset m v {b}) (v 0) b (-(m : ℤ))
          (simplexHADecodeSubset_two m v {b} (Finset.singleton_nonempty b)
            (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
          (simplexHADecodeSubset_min m v {b}
            (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm
          (simplexHADecodeSubset_max m v {b} (Finset.singleton_nonempty b)
            (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm (by
              have hc := simplexHADecodeSubset_card m v {b}
                (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
              simp only [Finset.card_singleton] at hc
              omega) := by
  have h := simplexHADegreeLift_generator A s m v b hb (-(m : ℤ))
    (serreCubeTopGeneratorIndex m) (serreCubeTopGeneratorIndex_degree m)
  have ht := congrArg (fun w => simplexHADegreeLift A s m v b hb (-(m : ℤ)) w)
    (serreCubeTopGeneratorIndex_cast A m)
  exact eq_of_heq ((heq_of_eq (ht.symm.trans h)).trans
    ((complexElement_degree_cast_heq A _ (serreCubeTopGeneratorIndex_degree m) _).trans
      (simplexHAGeneratorValue_top_heq A s m v b hb)))

end SerrePositivity.KST.SConstruction
