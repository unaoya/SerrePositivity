module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitTetrahedronBoundary

/-!
概要：元の四面の境界データを、同じ全選択パラメータを持つ実三角形証拠へ移す。
方針：元の固定三面・第零面の実持ち上げをそのまま用い、共通頂点を三つの実評価で固定する。
規約：実持ち上げと全係数を保持。使われ方：四面の指定比較の共通頂点での表示。
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

/-- 元の面 012 の全実持ち上げ。 -/
def CoherentColimitUnitTetrahedronBoundary.w012 :=
  coherentColimitUnitPointedFixedFaceTriangleWitness B T k 3 (by decide) D.triangle012 D.face012

/-- 元の面 123 の全実持ち上げ。 -/
def CoherentColimitUnitTetrahedronBoundary.w123 :=
  coherentColimitUnitZeroFaceTriangleWitness B T k D.edge01 D.firstEdge D.triangle123 D.face123

/-- 元の面 013 の全実持ち上げ。 -/
def CoherentColimitUnitTetrahedronBoundary.w013 :=
  coherentColimitUnitPointedFixedFaceTriangleWitness B T k 2 (by decide) D.triangle013 D.face013

/-- 元の面 023 の全実持ち上げ。 -/
def CoherentColimitUnitTetrahedronBoundary.w023 :=
  coherentColimitUnitPointedFixedFaceTriangleWitness B T k 1 (by decide) D.triangle023 D.face023

/-- 同じ元の全三単体の共通頂点一は、元の面 012 の実中間評価。 -/
def CoherentColimitUnitTetrahedronBoundary.source1 := D.w012.middle

/-- 同じ元の全三単体の共通頂点二は、元の面 012 の実終点評価。 -/
def CoherentColimitUnitTetrahedronBoundary.source2 := D.w012.endpoint

/-- 同じ元の全三単体の共通頂点三は、元の面 013 の実終点評価。 -/
def CoherentColimitUnitTetrahedronBoundary.source3 := D.w013.endpoint

/-- 共通頂点一の元の底の射影。 -/
lemma CoherentColimitUnitTetrahedronBoundary.source1_over :
    D.source1 ≫ leftUnstraighteningProjection D.vertex1 =
      fst (leftUnstraightening F) (coherentColimitUnitPointedTetrahedronChoice B T k) ≫
        leftUnstraighteningProjection F := D.w012.middle_projection

/-- 共通頂点二の元の底の射影。 -/
lemma CoherentColimitUnitTetrahedronBoundary.source2_over :
    D.source2 ≫ leftUnstraighteningProjection D.vertex2 =
      fst (leftUnstraightening F) (coherentColimitUnitPointedTetrahedronChoice B T k) ≫
        leftUnstraighteningProjection F := D.w012.endpoint_projection

/-- 共通頂点三の元の底の射影。 -/
lemma CoherentColimitUnitTetrahedronBoundary.source3_over :
    D.source3 ≫ leftUnstraighteningProjection D.vertex3 =
      fst (leftUnstraightening F) (coherentColimitUnitPointedTetrahedronChoice B T k) ≫
        leftUnstraighteningProjection F := D.w013.endpoint_projection

end SerrePositivity.InfinityCategories.F2
