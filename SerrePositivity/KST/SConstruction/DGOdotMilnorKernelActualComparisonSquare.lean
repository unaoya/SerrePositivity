module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorKernelNullUpperTriangle
public import SerrePositivity.KST.SConstruction.DGOdotTailKernelComparisonSquare

/-!
概要：無条件の V 経由上二単体を、K-S2 の元下二単体と固定 S 内で貼る。
方針：同じ共有対角の等号を証明し、供給済みの比較四角形へ代入する。
規約：上下の元全二単体を厳密に保持し、K-S2 の定義は変更しない。
使われ方：共通 S 長方形の左比較面と kernel_vertex の実構成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open scoped Simplicial
private lemma sharedDiagonal {X : SSet.{v}} {a b c e : X _⦋0⦌}
    {l : X.Edge a b} {r : X.Edge b c} {l' : X.Edge a e} {r' : X.Edge e c}
    {d : X.Edge a c} (T : SSet.Edge.CompStruct l r d) (U : SSet.Edge.CompStruct l' r' d) :
    stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm T.simplex =
      stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm U.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, T.d₁,
    stdSimplex.δ_comp_yonedaEquiv_symm, U.d₁]

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d

/-- 概要：無条件の V 経由上二単体の実 S 図式。
方針：元の合成証人を Yoneda で射として読む。
規約：二単体を選び直さない。使われ方：K-S2 の実貼合せへの上面入力。 -/
def dgOdotMilnorKernelNullUpperDiagram :
    (Δ[2] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  SSet.yonedaEquiv.symm (dgOdotMilnorKernelNullUpperTriangle R d).simplex

/-- 概要：元上下二単体は K-S2 の同じ厳密合成対角を共有する。
方針：両合成証人の中間面を回収する。
規約：辺代表の厳密等号。使われ方：元二単体の貼合せ条件。 -/
lemma dgOdotMilnorKernelNullUpperDiagram_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ dgOdotMilnorKernelNullUpperDiagram R d =
      stdSimplex.δ (1 : Fin 3) ≫ dgOdotTailKernelLiftTriangle R d :=
  sharedDiagonal (dgOdotMilnorKernelNullUpperTriangle R d) (dgOdotTailKernelLiftCompStruct R d)

/-- 概要：同じ元上下二単体を持つ無条件の実 S 比較四角形。
方針：K-S2 の供給済み貼合せへ元上二単体を代入する。
規約：元厚核包含・元実中央辺を保持。使われ方：共通長方形の左面。 -/
def dgOdotMilnorKernelActualComparisonSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  dgOdotTailKernelComparisonSquare R d (dgOdotMilnorKernelNullUpperDiagram R d)
    (dgOdotMilnorKernelNullUpperDiagram_diagonal R d)

/-- 概要：比較四角形の上全二単体は元 V 因子化のもの。
方針：同じ貼合せの第一制限を回収する。
規約：元全二単体の等号。使われ方：上指定二単体の保持。 -/
lemma dgOdotMilnorKernelActualComparisonSquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgOdotMilnorKernelActualComparisonSquare R d =
      dgOdotMilnorKernelNullUpperDiagram R d :=
  dgOdotTailKernelComparisonSquare_upper R d _ _

/-- 概要：比較四角形の下全二単体は K-S2 の元厳密合成のもの。
方針：同じ貼合せの第二制限を回収する。
規約：対角移送で変更しない。使われ方：下指定二単体の保持。 -/
lemma dgOdotMilnorKernelActualComparisonSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorKernelActualComparisonSquare R d =
      dgOdotTailKernelLiftTriangle R d :=
  dgOdotTailKernelComparisonSquare_lower R d _ _

/-- 概要：実比較面の四辺は元厚核包含・中央辺・V 因子化・V 包含そのもの。
方針：元上下全二単体の境界を回収する。
規約：四辺の全一単体を保持。使われ方：実右零化面との共有辺。 -/
lemma dgOdotMilnorKernelActualComparisonSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorKernelActualComparisonSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorKernelActualComparisonSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorKernelActualComparisonSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorKernelNullFactorInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorKernelActualComparisonSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullInputMap R (U))).edge := by
  have hL := dgOdotTailKernelComparisonSquare_lower_edges R d
    (dgOdotMilnorKernelNullUpperDiagram R d) (dgOdotMilnorKernelNullUpperDiagram_diagonal R d)
  have hU := dgOdotTailKernelComparisonSquare_upper_edges R d
    (dgOdotMilnorKernelNullUpperDiagram R d) (dgOdotMilnorKernelNullUpperDiagram_diagonal R d)
  refine ⟨hL.1, hL.2, ?_, ?_⟩
  · exact hU.1.trans ((stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans
      (congrArg SSet.yonedaEquiv.symm (dgOdotMilnorKernelNullUpperTriangle R d).d₂))
  · exact hU.2.trans ((stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans
      (congrArg SSet.yonedaEquiv.symm (dgOdotMilnorKernelNullUpperTriangle R d).d₀))

/-- 概要：実比較面の元始点は同じ厚核 S 入力。
方針：K-S2 の元頂点回収を使用する。
規約：ν 同値だけでなく頂点等号。使われ方：ActualRectangleInput.kernel_vertex。 -/
lemma dgOdotMilnorKernelActualComparisonSquare_kernel_vertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorKernelActualComparisonSquare R d) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d) :=
  dgOdotTailKernelComparisonSquare_kernel_vertex R d _ _

end SerrePositivity.KST.SConstruction
