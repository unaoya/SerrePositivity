module
public import SerrePositivity.KST.Spectra.S3ActualFaces
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualRectangle

/-!
概要：K-S• の同じ Milnor 入力・実商・完備化を保つ s3 の代入口。
方針：右面・外周・全長方形の三認証を明示引数にし、既存入力へ一度で代入する。
規約：実認証の構成は K-S• ③ の担当。この骨格からその存在は主張しない。
使われ方：K-B3 e に渡す二面の相殺と、元対角始域への屋根の回収。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Spectra.S3
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)

/-- 三認証到着時の一回の代入。始域照合は実平坦核にのみ要求する。 -/
def milnorActualInput
    (G : (Δ[2] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R)
    (br : VerdierSquareBoundaryIso (dgOdotMilnorActualRightDiagram R d h).square
      (verdierRectangleFace 0 ≫ G ≫ dgKInputPerfectNu R))
    (bo : VerdierSquareBoundaryIso (dgOdotMilnorActualOuterDiagram R d h).square
      (verdierRectangleFace 1 ≫ G ≫ dgKInputPerfectNu R))
    (b : VerdierRectangleBoundaryIso (G ≫ dgKInputPerfectNu R)
      (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram)
    (er : VerdierSquareDiagramIso (dgOdotMilnorActualRightDiagram R d h).square
      (verdierRectangleFace 0 ≫ G ≫ dgKInputPerfectNu R) br)
    (eo : VerdierSquareDiagramIso (dgOdotMilnorActualOuterDiagram R d h).square
      (verdierRectangleFace 1 ≫ G ≫ dgKInputPerfectNu R) bo)
    (e : VerdierRectangleDiagramIso (G ≫ dgKInputPerfectNu R)
      (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram b)
    (hk : squareVertex ((β_ _ _).hom ≫ pastingSquare G 2) 0 0 =
      coherentNerveVertex (dgOdotMilnorFlatKernelInput R d)) :
    DGOdotMilnorActualRectangleInput R d h :=
  ⟨G, br, er, bo, eo, b, e, hk⟩

variable {R d h} (v : DGOdotMilnorActualRectangleInput R d h)

/-- 実 S 比較面と元の LT 比較面の双方を、同じ三認証から得る。 -/
theorem milnorActual_isPullback
    {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hE : IsPerfectLocalizingInvariant E) :
    IsPullbackSquare (((β_ _ _).hom ≫ pastingSquare v.diagram 2) ≫
      dgKInputPerfectNu R ≫ E) ∧
    IsPullbackSquare (((β_ _ _).hom ≫
      pastingSquare (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram 2) ≫ E) :=
  actualFaces_isPullback v.diagram (dgOdotMilnorActualRightDiagram R d h)
    (dgOdotMilnorActualOuterDiagram R d h) v.rightBoundary v.outerBoundary v.boundary
    v.rightComparison v.outerComparison v.comparison hE

/-- 同じ実平坦核の頂点から、構成済みの元対角始域への屋根を回収する。 -/
def milnorSourceRoof : RelativePerfectVerdierSourceRoof (dgKInputPerfectNu R)
    (coherentNerveVertex (dgOdotDiagonalSourceInput R d))
    (squareVertex ((β_ _ _).hom ≫ pastingSquare v.diagram 2) 0 0) := v.sourceRoof

/-- 始域の値の回収には全長方形比較の同じ成分を使用する。 -/
def milnorSourceValueIso (E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}) :
    VertexIso ((dgKInputPerfectNu R ≫ E).app _
      (coherentNerveVertex (dgOdotDiagonalSourceInput R d)))
      (squareVertex (((β_ _ _).hom ≫
        pastingSquare (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram 2) ≫ E) 0 0) :=
  actualSourceValueIso v.boundary v.comparison (milnorSourceRoof v) E

/-- 指定された上下の合成二単体への制限をそのまま回収する。 -/
theorem milnorComparison_triangles :
    v.comparison.comparison.precomp (pastingBottomTriangle (𝟙 _)) = v.boundary.bottom ∧
    v.comparison.comparison.precomp (pastingTopTriangle (𝟙 _)) = v.boundary.top :=
  ⟨v.comparison.bottom_eq, v.comparison.top_eq⟩

end SerrePositivity.KST.Spectra.S3
