module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorKernelActualComparisonSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareTransposeEdges
public import SerrePositivity.KST.LocalizingInvariants.RelativeVerdierDiagramComparison

/-!
概要：元上下比較二単体と V の実零化面を保持する共通 S 長方形を作る。
方針：二面を転置し、指定した上下合成二単体を Sp 正本の延長へ渡す。
規約：比較面の上下二単体と長方形自体の上下合成二単体は区別して全て保持する。
使われ方：ActualRectangleInput の diagram・kernel_vertex。三認証は別工程。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
private lemma recoverTransposedRight {X : SSet.{u}}
    {L N : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    {b t : (Δ[2] : SSet.{u}) ⟶ X}
    (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle L ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ N) b t) :
    (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0 = N := by
  rw [r.right_eq, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "C" => dgOdotMilnorKernelActualComparisonSquare R d
local notation "N" => dgIdentityHomGluingNullDomainSquare R (U)

/-- 概要：長方形自体の下境界は元 V 因子化と V の全対象商包含の合成。
方針：同じ固定 S の厳密合成証人を使用する。
規約：比較面の上二単体とは別。使われ方：全長方形の指定下三角形。 -/
def dgOdotMilnorActualRectangleBottomTriangle : SSet.Edge.CompStruct
    (X := dgKInputInfinity.{u, u + 1} R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorKernelNullFactorInputMap R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgIdentityHomGluingNullInput R (U))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorKernelNullFactorInputMap R d ≫
      dgFixedNullLeft R (A := dgIdentityHomGluingNullInput R (U)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct _ _

/-- 概要：長方形自体の上境界は元実中央辺と同じ実 cone 差の合成。
方針：同じ固定 S の厳密合成証人を使用する。
規約：K-S2 の比較面下二単体とは別。使われ方：全長方形の指定上三角形。 -/
def dgOdotMilnorActualRectangleTopTriangle : SSet.Edge.CompStruct
    (X := dgKInputInfinity.{u, u + 1} R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingDifferenceInputMap R (U)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d ≫
      dgIdentityHomGluingDifferenceInputMap R (U))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct _ _

/-- 概要：元比較面と V の実零化面を元上下合成三角形付きで貼る。
方針：同じ共有辺の等号を Sp 正本の全境界延長へ渡す。
規約：三認証はここでは主張しない。使われ方：共通 S 長方形の実図式。 -/
def dgOdotMilnorActualSPastingRectangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle
    ((β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫ (C))
    ((β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫ (N))
    (SSet.yonedaEquiv.symm (dgOdotMilnorActualRectangleBottomTriangle R d).simplex)
    (SSet.yonedaEquiv.symm (dgOdotMilnorActualRectangleTopTriangle R d).simplex) := by
  have hC := dgOdotMilnorKernelActualComparisonSquare_edges R d
  have hN := dgIdentityHomGluingNullDomainSquare_edges R (U)
  apply Classical.choice
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.nonempty_squarePastingRectangle
  · exact ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_right (C)).trans hC.2.2.2).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_left (N)).trans hN.1).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom (C)).trans
      (hC.2.2.1.trans (dgOdotMilnorActualRectangleBottomTriangle R d).δ_two_yonedaEquiv_symm.symm)
  · exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom (N)).trans
      (hN.2.2.1.trans (dgOdotMilnorActualRectangleBottomTriangle R d).δ_zero_yonedaEquiv_symm.symm)
  · exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_top (C)).trans
      (hC.2.1.trans (dgOdotMilnorActualRectangleTopTriangle R d).δ_two_yonedaEquiv_symm.symm)
  · exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_top (N)).trans
      (hN.2.1.trans (dgOdotMilnorActualRectangleTopTriangle R d).δ_zero_yonedaEquiv_symm.symm)

/-- 概要：同じ元四辺と上下三角形を持つ無条件の共通 S 長方形。
方針：元貼合せの全図式を取り出す。
規約：固定 ν の三認証は別。使われ方：ActualRectangleInput.diagram。 -/
def dgOdotMilnorActualRectangleDiagram :
    (Δ[2] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  (dgOdotMilnorActualSPastingRectangle R d).diagram

/-- 概要：同じ長方形の比較面は元上下二単体を持つ実四角形そのもの。
方針：元貼合せの左面回収と転置の二乗を使う。
規約：全四角形の等号。使われ方：指定比較二単体と始点の回収。 -/
lemma dgOdotMilnorActualRectangleDiagram_comparison :
    (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorActualRectangleDiagram R d) 2 = (C) := by
  change (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorActualSPastingRectangle R d).diagram 2 = _
  rw [(dgOdotMilnorActualSPastingRectangle R d).left_eq, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：同じ長方形の実右面は V の同じ実零化四角形。
方針：元貼合せの右面回収と転置の二乗を使う。
規約：元四辺と全二胞体の等号。使われ方：右面 Verdier 認証の実側。 -/
lemma dgOdotMilnorActualRectangleDiagram_right :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ dgOdotMilnorActualRectangleDiagram R d = (N) := by
  change (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorActualSPastingRectangle R d).diagram 0 = _
  exact recoverTransposedRight (dgOdotMilnorActualSPastingRectangle R d)

/-- 概要：同じ実長方形の比較面の始点は元厚核入力。
方針：元比較面の回収と K-S2 の元頂点等号を使用する。
規約：追加の頂点同値ではない。使われ方：ActualRectangleInput.kernel_vertex。 -/
lemma dgOdotMilnorActualRectangleDiagram_kernel_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorActualRectangleDiagram R d) 2) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d) := by
  rw [dgOdotMilnorActualRectangleDiagram_comparison]
  exact dgOdotMilnorKernelActualComparisonSquare_kernel_vertex R d

/-- 概要：長方形比較面の上二単体は元 V 因子化の二単体を保持する。
方針：元比較面とその上三角形の回収を合成する。
規約：指定全二単体の等号。使われ方：固定 ν 全比較の上面入力。 -/
lemma dgOdotMilnorActualRectangleDiagram_comparison_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorActualRectangleDiagram R d) 2 =
      dgOdotMilnorKernelNullUpperDiagram R d := by
  rw [dgOdotMilnorActualRectangleDiagram_comparison]
  exact dgOdotMilnorKernelActualComparisonSquare_upper R d

/-- 概要：長方形比較面の下二単体は K-S2 の元厳密合成を保持する。
方針：元比較面とその下三角形の回収を合成する。
規約：元指定全二単体の等号。使われ方：固定 ν 全比較の下指定面。 -/
lemma dgOdotMilnorActualRectangleDiagram_comparison_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorActualRectangleDiagram R d) 2 =
      dgOdotTailKernelLiftTriangle R d := by
  rw [dgOdotMilnorActualRectangleDiagram_comparison]
  exact dgOdotMilnorKernelActualComparisonSquare_lower R d

/-- 概要：長方形自体の元下合成二単体も厳密に保持する。
方針：同じ貼合せの下三角形を回収する。
規約：比較面の下三角形とは区別。使われ方：全長方形認証の bottom 欄。 -/
lemma dgOdotMilnorActualRectangleDiagram_bottom :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle (dgOdotMilnorActualRectangleDiagram R d) =
      SSet.yonedaEquiv.symm (dgOdotMilnorActualRectangleBottomTriangle R d).simplex :=
  (dgOdotMilnorActualSPastingRectangle R d).bottom_eq

/-- 概要：長方形自体の元上合成二単体も厳密に保持する。
方針：同じ貼合せの上三角形を回収する。
規約：比較面の上三角形とは区別。使われ方：全長方形認証の top 欄。 -/
lemma dgOdotMilnorActualRectangleDiagram_top :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (dgOdotMilnorActualRectangleDiagram R d) =
      SSet.yonedaEquiv.symm (dgOdotMilnorActualRectangleTopTriangle R d).simplex :=
  (dgOdotMilnorActualSPastingRectangle R d).top_eq

end SerrePositivity.KST.SConstruction
