module
public import SerrePositivity.KST.SConstruction.SimplexHAZeroFaceRestriction
public import SerrePositivity.KST.SConstruction.DGRightCycleComposition
public import SerrePositivity.KST.SConstruction.SimplexHAZeroChainLift

/-! # 元の一端点追加生成元と HA 辺との右合成
概要：元の一端点追加生成元の HA 値を、前段の生成元値と同じ閉零辺の右合成へ戻す。
方針：右側一点の bead 値と連結語の生の値を、元の実右合成鎖射の次数移送で比較する。
規約：元の閉零辺と豊穣順を保持。使われ方：右端一面への全次数制限の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の右側一点の bead の生の HA 値は、同じ元の HA 辺。 -/
lemma simplexHABeadTail_singleton_rawValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (a b : Fin (n + 1)) (hab : a < b) :
    simplexHABeadWordRawValue A s.toSimplexData
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail {b} (Finset.singleton_nonempty b) a
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hab)) = s.edgeHom a b hab := by
  have hI : 2 ≤ ({a, b} : Finset (Fin (n + 1))).card := by simp [ne_of_lt hab]
  have ha : a = ({a, b} : Finset (Fin (n + 1))).min'
      (Finset.card_pos.mp (by omega)) := by
    symm
    exact (Finset.min'_eq_iff _ _ _).mpr (by simp [hab.le])
  have hb : b = ({a, b} : Finset (Fin (n + 1))).max'
      (Finset.card_pos.mp (by omega)) := by
    symm
    exact (Finset.max'_eq_iff _ _ _).mpr (by simp [hab.le])
  change serreCubeOrientationSign 0 • simplexHABeadWordValue A s.toSimplexData
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail {b} (Finset.singleton_nonempty b) a
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hab)) = _
  rw [serreCubeOrientationSign_zero, one_smul]
  exact (simplexHABeadTail_value A s.toSimplexData {b} (Finset.singleton_nonempty b) a
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hab) hI ha
      (by simpa only [Finset.max'_singleton] using hb)).trans (by rfl)

/-- 元の一端点追加生成元の値は、前段の値と同じ閉零辺による実右合成の値。 -/
lemma simplexHAGeneratorValue_point_one_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 2) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last (m + 1)) < b) :
    HEq (simplexHAGeneratorValue A s.toSimplexData (m + 1) (i, 1) v b hb)
      ((dgRightCycleComposition A (x := s.obj (v 0))
        (s.edgeCycle (v (Fin.last (m + 1))) b hb)).f (serreCubeGeneratorDegree m i)
        (simplexHAGeneratorValue A s.toSimplexData m i (Fin.castSuccOrderEmb.trans v)
          (v (Fin.last (m + 1))) (simplexHADecodePrefix_last m v))) := by
  let r := v (Fin.last (m + 1))
  let p : ℤ := -(serreCubeGeneratorFreeDimension m i : ℤ)
  let left : GradedHom A (s.obj (v 0)) (s.obj r) p :=
    simplexHABeadWordRawValue A s.toSimplexData (simplexHAGeneratorWord m i
      (Fin.castSuccOrderEmb.trans v) r (simplexHADecodePrefix_last m v))
  let right : GradedHom A (s.obj r) (s.obj b) 0 :=
    simplexHABeadWordRawValue A s.toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail {b}
      (Finset.singleton_nonempty b) r (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
  let R := dgRightCycleComposition A (x := s.obj (v 0)) (s.edgeCycle r b hb)
  have hr : forward A left right (add_zero p) = R.f p left :=
    (congrArg (fun g => forward A left g (add_zero p))
      (simplexHABeadTail_singleton_rawValue A s r b hb)).trans
        (dgRightCycleComposition_apply A (s.edgeCycle r b hb) p left).symm
  have ht := complexMap_degree_cast A R (serreCubeGeneratorDegree_freeDimension m i).symm left
  have hm : HEq (R.f (serreCubeGeneratorDegree m i)
      (simplexHAGeneratorValue A s.toSimplexData m i (Fin.castSuccOrderEmb.trans v) r
        (simplexHADecodePrefix_last m v))) (R.f p left) :=
    (heq_of_eq ht).trans (complexElement_degree_cast_heq A _
      (serreCubeGeneratorDegree_freeDimension m i).symm _)
  exact (complexElement_degree_cast_heq A _
    (serreCubeGeneratorDegree_freeDimension (m + 1) (i, 1)).symm _).trans
      ((simplexHABeadWordDecode_one_rawValue A s.toSimplexData m i v {b}
        (Finset.singleton_nonempty b) (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).trans
          ((heq_of_eq hr).trans hm.symm))

end SerrePositivity.KST.SConstruction
