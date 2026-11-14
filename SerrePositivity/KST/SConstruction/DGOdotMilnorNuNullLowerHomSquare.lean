module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullIntervalEdges
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization

/-!
概要：元実／絶対下三角形の全 Hom を指定商比較付きの同じ零 Hom 正方形に置く。
方針：同じ可縮成分の終頂点性で四つの元実辺を全て固定した正方形を作る。
規約：元全 Hom・元商比較を保持。coherent nerve の全図式比較とは別工程。
使われ方：元下二胞体と指定商境界を保つ相対延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元実／絶対下三角形の Hom と指定商比較を四辺に持つ実零 Hom 正方形。
方針：同じ可縮成分の終頂点性で元四辺の可換性を認証し実現する。
規約：四辺は元の全区間写像そのもの。使われ方：指定下二胞体の相対比較。 -/
lemma exists_dgOdotMilnorNuNullLowerHomSquare :
    ∃ Q : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ DGOdotMilnorNuNullCoherenceSpace R d,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q = dgOdotMilnorNuNullTriangleInterval R d 1 ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q = dgOdotMilnorNuAbsoluteTriangleInterval R d h 1 ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ Q =
        SSet.yonedaEquiv.symm (dgOdotMilnorNuNullDiagonalComparisonEdge R d h).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q = dgOdotMilnorNuProjectionNullFactor R d h := by
  letI : KanComplex (DGOdotMilnorNuNullCoherenceSpace R d) :=
    (dgOdotMilnorNuNullCoherenceSpace_contractible R d h).kanComplex
  let b := dgOdotMilnorNuNullTriangleIntervalEdge R d 1
  let t := dgOdotMilnorNuAbsoluteTriangleIntervalEdge R d h 1
  let l := dgOdotMilnorNuNullDiagonalComparisonEdge R d h
  let r := dgOdotMilnorNuProjectionNullIntervalEdge R d h
  have hc : SSet.Truncated.HomotopyCategory.homMk b.toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk r.toTruncated =
      SSet.Truncated.HomotopyCategory.homMk l.toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk t.toTruncated :=
    ((dgOdotMilnorNuNullCoherenceSpace_contractible R d h).isTerminalVertex
      ((dgOdotMilnorNuAbsoluteTriangleFactor R d h 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}))).isTerminalHo.hom_ext _ _
  obtain ⟨Q, hb, ht, hl, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm
    b.toTruncated t.toTruncated l.toTruncated r.toTruncated hc
  exact ⟨Q, hb.trans (dgOdotMilnorNuNullTriangleIntervalEdge_parameter R d 1),
    ht.trans (dgOdotMilnorNuAbsoluteTriangleIntervalEdge_parameter R d h 1), hl,
    hr.trans (dgOdotMilnorNuProjectionNullIntervalEdge_parameter R d h)⟩

/-- 概要：元の四辺を保持する選択された同じ零 Hom 比較正方形。
方針：元四辺を全て固定した存在証明から一つを取る。
規約：後の回収でも同じ正方形を使う。使われ方：下二胞体の相対延長。 -/
def dgOdotMilnorNuNullLowerHomSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ DGOdotMilnorNuNullCoherenceSpace R d :=
  (exists_dgOdotMilnorNuNullLowerHomSquare R d h).choose

/-- 概要：同じ零 Hom 比較正方形は指定した元四辺を厳密に回収する。
方針：元の四辺固定存在証明を使う。
規約：元二胞体の区間と指定商比較の全単体。使われ方：coherent 面の元境界保持。 -/
lemma dgOdotMilnorNuNullLowerHomSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorNuNullLowerHomSquare R d h =
        dgOdotMilnorNuNullTriangleInterval R d 1 ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorNuNullLowerHomSquare R d h =
        dgOdotMilnorNuAbsoluteTriangleInterval R d h 1 ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorNuNullLowerHomSquare R d h =
        SSet.yonedaEquiv.symm (dgOdotMilnorNuNullDiagonalComparisonEdge R d h).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorNuNullLowerHomSquare R d h =
        dgOdotMilnorNuProjectionNullFactor R d h :=
  (exists_dgOdotMilnorNuNullLowerHomSquare R d h).choose_spec

/-- 概要：同じ正方形の実側の辺は元実下三角形の全 Hom 因子分解を回収する。
方針：同じ元辺回収と区間同型の順逆式を合成する。
規約：元全高次 Hom の等号。使われ方：元実二胞体の厳密保持。 -/
lemma dgOdotMilnorNuNullLowerHomSquare_actual_fullHom :
    dgOdotMilnorNuNullPathIntervalIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫
        dgOdotMilnorNuNullLowerHomSquare R d h = dgOdotMilnorNuNullTriangleFactor R d 1 :=
  (congrArg (fun f => dgOdotMilnorNuNullPathIntervalIso.hom ≫ f)
    (dgOdotMilnorNuNullLowerHomSquare_edges R d h).1).trans
      (dgOdotMilnorNuNullTriangleInterval_recover R d 1)

/-- 概要：同じ正方形の絶対側の辺は元絶対下三角形の全 Hom 因子分解を回収する。
方針：同じ元辺回収と区間の順逆式を合成する。
規約：元全高次 Hom の等号。使われ方：元絶対二胞体の厳密保持。 -/
lemma dgOdotMilnorNuNullLowerHomSquare_absolute_fullHom :
    dgOdotMilnorNuNullPathIntervalIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫
        dgOdotMilnorNuNullLowerHomSquare R d h =
      dgOdotMilnorNuAbsoluteTriangleFactor R d h 1 :=
  (congrArg (fun f => dgOdotMilnorNuNullPathIntervalIso.hom ≫ f)
    (dgOdotMilnorNuNullLowerHomSquare_edges R d h).2.1).trans
      (dgOdotMilnorNuAbsoluteTriangleInterval_recover R d h 1)

end SerrePositivity.KST.SConstruction
