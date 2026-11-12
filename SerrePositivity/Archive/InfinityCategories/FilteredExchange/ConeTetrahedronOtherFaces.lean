module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConeTetrahedronParameter
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SimplexConeIndexNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleRightConeEdges
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.AppendEdgeConeMiddle
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan

/-!
概要：元の実四面体の残る三面を、元の三角形の三辺への終点追加として計算する。
方針：標準単体錐の全添字自然性を元の同じ三角形へ適用する。
規約：実全面を保持。使われ方：元の指定合成図式との同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の四面体の三つの残る面は、同じ実三角形の元の辺へ終点を追加した全面。 -/
lemma coneTetrahedronParameter_face (P : SSet.{u}) (i : Fin 3) :
    (stdSimplex.δ i.castSucc ▷ P) ≫ coneTetrahedronParameter P =
      simplexConeParameter 1 P ≫
        joinMap ((stdSimplex.δ i ▷ P) ≫ triangleRightConeParameter P) (𝟙 Δ[0]) ≫
          appendEdgeConeCoordinatesInverse (Δ[1] ⊗ P) := by
  have hf : (stdSimplex.δ i.castSucc ▷ P) ≫ simplexConeParameter 2 P =
      simplexConeParameter 1 P ≫ joinMap (stdSimplex.δ i ▷ P) (𝟙 Δ[0]) := by
    simpa only [pinchedExtend_δ, CosimplicialObject.δ] using
      simplexConeParameter_index_naturality (SimplexCategory.δ i) P
  rw [coneTetrahedronParameter, ← Category.assoc, hf, Category.assoc]
  have hj : joinMap (stdSimplex.δ i ▷ P) (𝟙 (Δ[0] : SSet.{u})) ≫
      joinMap (triangleRightConeParameter P) (𝟙 Δ[0]) ≫
        appendEdgeConeCoordinatesInverse (Δ[1] ⊗ P) =
    joinMap ((stdSimplex.δ i ▷ P) ≫ triangleRightConeParameter P) (𝟙 Δ[0]) ≫
      appendEdgeConeCoordinatesInverse (Δ[1] ⊗ P) := by
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp]
  exact congrArg (fun k => simplexConeParameter 1 P ≫ k) hj

/-- 元の 013 面は、同じ実追加辺の終点に沿う標準三角形錐。 -/
lemma coneTetrahedronParameter_face013 (P : SSet.{u}) :
    (stdSimplex.δ (2 : Fin 4) ▷ P) ≫ coneTetrahedronParameter P =
      simplexConeParameter 1 P ≫ joinMap (𝟙 (Δ[1] ⊗ P)) (stdSimplex.δ (0 : Fin 2)) := by
  have h := coneTetrahedronParameter_face P (2 : Fin 3)
  rw [triangleRightConeParameter_first, appendEdgeConeCoordinatesInverse_middle] at h
  exact h

end SerrePositivity.InfinityCategories.F2
