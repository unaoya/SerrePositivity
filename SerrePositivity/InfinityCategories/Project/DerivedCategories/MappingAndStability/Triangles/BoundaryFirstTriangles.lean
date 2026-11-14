module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.JoinFirstTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanBoundaryData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation

/-! # 境界の最初の頂点の二三角形

概要：最後の境界面の最初の三角形は、境界の最初の頂点の余錐の三角形である。
方針：最初の三角形の join 公式と、最後の面の最初の頂点の評価を合成する。
規約：境界は右因子。使われ方：D7 の標準 cofiber の固定三角形の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：最後の境界面の最初の頂点は境界全体の最初の頂点。
方針：境界の頂点の評価式で最後の点を飛ばす。
規約：零番目の頂点は保たれる。使われ方：指定余錐を既知面で回収する。 -/
lemma boundaryVertex_first_face_last (n : ℕ) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
        SSet.boundary.ι.{u} (Fin.last (n + 1)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 := by
  simpa only [Fin.succAbove_last, Fin.castSucc_zero] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.vertex_face.{u} (Fin.last (n + 1)) 0

/-- 概要：大きいセルの最後の既知面は可変因子の最後の境界面に対応する。
方針：面番号の値から二を引いて計算する。
規約：固定二点の後の面番号。使われ方：境界への面の持ち上げの簡約。 -/
lemma spanSuffixFaceIndex_last (n : ℕ)
    (h : Fin.last (n + 3) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaceIndex (Fin.last (n + 3)) h = Fin.last (n + 1) := by
  apply Fin.ext
  change n + 3 - 2 = n + 1
  omega

/-- 概要：左の最後の既知面の最初の三角形は、最初の頂点の余錐三角形。
方針：最初の三角形の join 公式と境界頂点の評価を使う。
規約：固定二点を保つ。使われ方：左の余錐の成分の回収。 -/
lemma spanBoundaryLeftLift_first_triangle (n : ℕ)
    (h : Fin.last (n + 3) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift.{u} n (Fin.last (n + 3)) h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift
  rw [spanSuffixFaceIndex_last]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_first_triangle, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, boundaryVertex_first_face_last]

/-- 概要：右の最後の既知面の最初の三角形は、最初の頂点の余錐三角形。
方針：最初の三角形の join 公式と境界頂点の評価を使う。
規約：固定二点を保つ。使われ方：右の余錐の成分の回収。 -/
lemma spanBoundaryRightLift_first_triangle (n : ℕ)
    (h : Fin.last (n + 3) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift.{u} n (Fin.last (n + 3)) h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift
  rw [spanSuffixFaceIndex_last]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_first_triangle, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, boundaryVertex_first_face_last]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
