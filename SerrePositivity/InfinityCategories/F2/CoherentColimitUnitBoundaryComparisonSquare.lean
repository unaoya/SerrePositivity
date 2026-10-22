module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitBoundaryFixedFaceFormulas
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitBoundaryZeroFaceFormula
public import SerrePositivity.InfinityCategories.F2.FunctorIsoCompositionNatIso
public import SerrePositivity.InfinityCategories.F2.FunctorTetrahedronEdgeComparisonSquare

/-!
概要：元の四面の全実中間点・全実終点を、元の全三単体の共通頂点へ厳密に同定する。
方針：六共有辺の実始点・実終点の等式を同じ四面へ適用する。
規約：全係数と底の射影を保持。使われ方：四面の式を同じ六比較へ正規化する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle l r d} {k : Fin 3}
  (D : CoherentColimitUnitTetrahedronBoundary B T k)

local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F

local notation "x₀" => relativeFunctorVertex (leftUnstraighteningProjection F) p
  (fst (leftUnstraightening F) K) rfl

local notation "P01" => functorHomotopyRelativePost D.edge01 p
local notation "P12" => functorHomotopyRelativePost D.edge12 p
local notation "P23" => functorHomotopyRelativePost D.edge23 p
local notation "P02" => functorHomotopyRelativePost D.edge02 p
local notation "P13" => functorHomotopyRelativePost D.edge13 p
local notation "P03" => functorHomotopyRelativePost D.edge03 p
local notation "A012" => functorIsoCompositionNatIso
  (functorTriangleSequentialPostComparison D.triangle012 p)
local notation "A123" => functorIsoCompositionNatIso
  (functorTriangleSequentialPostComparison D.triangle123 p)
local notation "A013" => functorIsoCompositionNatIso
  (functorTriangleSequentialPostComparison D.triangle013 p)
local notation "A023" => functorIsoCompositionNatIso
  (functorTriangleSequentialPostComparison D.triangle023 p)

/-- 元の同じ全単位三単体の四面の指定比較は、共通の六辺上で厳密に可換する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.comparison_square :
    (functorTriangleSequentialPostComparison D.triangle013 p).app x₀ ≪≫
        (functorTriangleSequentialPostComparison D.triangle123 p).app ((P01).app _ x₀) =
      (functorTriangleSequentialPostComparison D.triangle023 p).app x₀ ≪≫
        VertexIso.map ((functorTriangleSequentialPostComparison D.triangle012 p).app x₀) P23 := by
  have h := functorTetrahedronIso_square_of_edge_comparisons
    (hoFunctor.map P01).toFunctor (hoFunctor.map P12).toFunctor (hoFunctor.map P23).toFunctor
    (hoFunctor.map P02).toFunctor (hoFunctor.map P13).toFunctor (hoFunctor.map P03).toFunctor
    A012 A123 A013 A023 (SSet.HomotopyCategory.mk x₀)
    (SSet.HomotopyCategory.mk D.x1) (SSet.HomotopyCategory.mk D.x2) (SSet.HomotopyCategory.mk D.x3)
    D.comparison01 D.comparison12 D.comparison23 D.comparison02 D.comparison13 D.comparison03
    (by simpa only [functorIsoCompositionNatIso_app, VertexIso.map] using D.face012_comparison)
    (by simpa only [functorIsoCompositionNatIso_app, VertexIso.map] using D.face123_comparison)
    (by simpa only [functorIsoCompositionNatIso_app, VertexIso.map] using D.face013_comparison)
    (by simpa only [functorIsoCompositionNatIso_app, VertexIso.map] using D.face023_comparison)
  change (A013).app (SSet.HomotopyCategory.mk x₀) ≪≫
      (A123).app (SSet.HomotopyCategory.mk ((P01).app _ x₀)) =
    (A023).app (SSet.HomotopyCategory.mk x₀) ≪≫
      (hoFunctor.map P23).toFunctor.mapIso ((A012).app (SSet.HomotopyCategory.mk x₀)) at h
  simpa only [functorIsoCompositionNatIso_app, VertexIso.map] using h

end SerrePositivity.InfinityCategories.F2
