module
public import SerrePositivity.KST.SConstruction.SimplexHAZeroEdgeCommutation
public import SerrePositivity.KST.SConstruction.SimplexHARightTailValues

/-! # 元の零端点・辺の右側集合を保つ source 微分像
概要：任意右側集合を保つ零端点・辺生成元で、元の source 微分像を語境界と同定。
方針：元の全辺付加生成元上の実微分可換性と、右側集合の語境界値の復元を合成する。
規約：右側集合内部の全境界を保持。使われ方：全生成元の逆 Hom 鎖射条件の零面部分。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の任意右側集合を保つ零端点・辺生成元の実 source 微分像は、同じ語の境界値。 -/
lemma simplexHARightTailPrefix_zeroEdge_source_boundary {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (hi : SerreCubeZeroEdgeIndex m i)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last m) < r) :
    let t := (T.erase (T.max' hT)).card
    let j := serreCubeGeneratorRightIndex m i t
    let w := simplexHARightTailPrefix m v T hT hb
    HEq (simplexHADegreeLift A s.toSimplexData (m + t) w.val (T.max' hT) w.property
      (serreCubeGeneratorDegree (m + t) j + 1)
      ((serreCubeComplex A (m + t)).d (serreCubeGeneratorDegree (m + t) j)
        (serreCubeGeneratorDegree (m + t) j + 1) (serreCubeGenerator A (m + t) j)))
      (simplexHABeadWordBoundaryValue A s.toSimplexData
        (simplexHABeadWordDecode m i v T hT hb)) := by
  let t := (T.erase (T.max' hT)).card
  let j := serreCubeGeneratorRightIndex m i t
  let w := simplexHARightTailPrefix m v T hT hb
  have h := simplexHADegreeLift_zeroEdge_source_boundary A s (m + t) j
    (serreCubeZeroEdgeIndex_right m i hi t) w.val (T.max' hT) w.property _ rfl
  have hc := complexElement_degree_cast_heq A
    (homObject A D (s.obj (w.val 0)) (s.obj (T.max' hT)))
    (congrArg (fun k : ℤ => k + 1)
      (serreCubeGeneratorDegree_freeDimension (m + t) j).symm)
    (simplexHABeadWordBoundaryValue A s.toSimplexData
      (simplexHAGeneratorWord (m + t) j w.val (T.max' hT) w.property))
  exact (heq_of_eq h).trans (hc.trans
    (simplexHARightTailPrefix_boundaryValue A s.toSimplexData m i v T hT hb))

end SerrePositivity.KST.SConstruction
