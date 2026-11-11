module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitCospan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismFaces

/-!
概要：元の単位三角柱を、共有面を厳密に保つ三つの三単体へ分解する。
方針：元の全円柱へ既存の標準分割を適用し、上下の全三角形も同定する。
規約：充填から再選択しない。使われ方：二三角形の指定比較の四面体による整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の全単位三角柱に含まれる、三つの指定三単体。 -/
def coherentColimitUnitTriangleTetrahedron (i : Fin 3) :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}) _⦋3⦌ :=
  triangleHomotopyTetrahedron (coherentColimitUnitTrianglePrism B T)
    (SSet.yonedaEquiv (𝟙 (Δ[2] : SSet.{u + 1}))) i

/-- 最初と中央の三単体は同じ全二単体を共有する。 -/
lemma coherentColimitUnitTriangleTetrahedron_glue_first :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 1
      (coherentColimitUnitTriangleTetrahedron B T 0) =
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 1
      (coherentColimitUnitTriangleTetrahedron B T 1) :=
  triangleHomotopyTetrahedron_glue_first _ _

/-- 中央と最後の三単体も同じ全二単体を共有する。 -/
lemma coherentColimitUnitTriangleTetrahedron_glue_last :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 2
      (coherentColimitUnitTriangleTetrahedron B T 1) =
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 2
      (coherentColimitUnitTriangleTetrahedron B T 2) :=
  triangleHomotopyTetrahedron_glue_last _ _

/-- 最初の三単体の終端面は、元の余極限二単体の定値図式族そのもの。 -/
lemma coherentColimitUnitTriangleTetrahedron_first :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
      (coherentColimitUnitTriangleTetrahedron B T 0) =
      SSet.yonedaEquiv (T.diagram ≫ coherentColimitFunctor B ≫
        constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}) := by
  have h := triangleHomotopyTetrahedron_first
    (coherentColimitUnitParameterHomotopy B T.diagram)
    (SSet.yonedaEquiv (𝟙 (Δ[2] : SSet.{u + 1})))
  simpa only [coherentColimitUnitTriangleTetrahedron, coherentColimitUnitTrianglePrism,
    coherentColimitUnitParameterHomotopy, ← SSet.yonedaEquiv_comp, Category.id_comp] using h

/-- 最後の三単体の始端面は、元の指定関手二単体そのもの。 -/
lemma coherentColimitUnitTriangleTetrahedron_last :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 3
      (coherentColimitUnitTriangleTetrahedron B T 2) = SSet.yonedaEquiv T.diagram := by
  have h := triangleHomotopyTetrahedron_last
    (coherentColimitUnitParameterHomotopy B T.diagram)
    (SSet.yonedaEquiv (𝟙 (Δ[2] : SSet.{u + 1})))
  simpa only [coherentColimitUnitTriangleTetrahedron, coherentColimitUnitTrianglePrism,
    coherentColimitUnitParameterHomotopy, ← SSet.yonedaEquiv_comp, Category.id_comp] using h

end SerrePositivity.InfinityCategories.F2
