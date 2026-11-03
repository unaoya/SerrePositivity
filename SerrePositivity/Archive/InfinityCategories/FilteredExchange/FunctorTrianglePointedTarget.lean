module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTrianglePointedLongWitness
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningConstantFamilyMap

/-!
概要：元の指定三角形比較に使う全持ち上げの終点を、元の二作用の厳密な合成へ同定する。
方針：元の長辺証拠の終点式を一点パラメータで制限する。
規約：元の二作用を保持。使われ方：第零面の全族比較の終点を native 合成へ接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の全 pointed 三角形の終点は、元の二つの選択済み全空間作用の厳密な合成。 -/
lemma functorTrianglePointedLift_target :
    simplexPrismVertex 2 2 (leftUnstraightening F) ≫ functorTrianglePointedLift T =
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy l)).val ≫
      (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy r)).val ≫
        pullback.fst pointedSpaceProjection J := by
  let V := coherentTriangleOfFunctorTriangle T
  let w := unstraighteningMappingTriangleLongWitness F G J
    (SSet.const (coherentVertexOfHomotopy l)) (SSet.const (coherentVertexOfHomotopy r))
    (SSet.const (coherentVertexOfHomotopy d)) V.diagram V.first V.second V.long
  have hl := functorTrianglePointedLift_long T (𝟙 (leftUnstraightening F))
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp] at hl
  have he : simplexPrismVertex 2 2 (leftUnstraightening F) =
      prismEndpoint 1 (leftUnstraightening F) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ leftUnstraightening F) := rfl
  rw [he, Category.assoc, hl, prismParameterRestriction]
  simp only [Category.assoc]
  rw [← Category.assoc (prismEndpoint 1 (leftUnstraightening F)), prismEndpoint_naturality]
  simp only [Category.assoc]
  change lift (𝟙 (leftUnstraightening F))
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
    prismEndpoint 1 (leftUnstraightening F ⊗ (Δ[0] : SSet.{u + 1})) ≫
    (α_ (Δ[1] : SSet.{u + 1}) (leftUnstraightening F) Δ[0]).inv ≫ w.prism = _
  rw [← Category.assoc (prismEndpoint 1 (leftUnstraightening F ⊗ (Δ[0] : SSet.{u + 1}))),
    prismEndpoint_associator_inv, w.target]
  rw [unstraighteningMappingConst_uncurry, unstraighteningMappingConst_uncurry]
  simp only [Category.assoc, lift_fst_assoc, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
