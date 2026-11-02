module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentFunctorTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationPointedTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSimplexPointedStart

/-!
概要：元の指定三角形比較に使った pointed 持ち上げを、元の全底上でそのまま保持する。
方針：選択済みの全三角形へ一点パラメータを代入し、元の底と初期値を回収する。
規約：持ち上げを選び直さない。使われ方：第零面における元の指定三角形比較。
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
local notation "L" => coherentTransformationTriangleLift F G J (coherentVertexOfHomotopy l)
  (coherentVertexOfHomotopy r) (coherentTriangleOfFunctorTriangle T)

/-- 元の指定三角形比較に用いた全 pointed 三角形へ、元の一点パラメータを代入する。 -/
def functorTrianglePointedLift :
    (Δ[2] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u} :=
  (Δ[2] ◁ lift (𝟙 (leftUnstraightening F))
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ (L).prism

/-- 指定比較の元の全持ち上げは、元の指定二単体の底を厳密に被覆する。 -/
lemma functorTrianglePointedLift_projection :
    functorTrianglePointedLift T ≫ pointedSpaceProjection =
      (Δ[2] ◁ leftUnstraighteningProjection F) ≫ functorSimplexDiagram T.diagram := by
  rw [functorTrianglePointedLift, Category.assoc, (L).projection]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の指定三角形比較の全持ち上げは、同じ元の pointed 始点を厳密に持つ。 -/
lemma functorTrianglePointedLift_initial :
    simplexPrismVertex 2 0 (leftUnstraightening F) ≫ functorTrianglePointedLift T =
      pullback.fst pointedSpaceProjection F := by
  have he : simplexPrismVertex 2 0 (leftUnstraightening F) =
      prismEndpoint 0 (leftUnstraightening F) ≫
        (stdSimplex.δ (2 : Fin 3) ▷ leftUnstraightening F) := rfl
  rw [he, functorTrianglePointedLift, Category.assoc]
  have hn : (stdSimplex.δ (2 : Fin 3) ▷ leftUnstraightening F) ≫
      (Δ[2] ◁ lift (𝟙 (leftUnstraightening F))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) =
      (Δ[1] ◁ lift (𝟙 (leftUnstraightening F))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
        (stdSimplex.δ (2 : Fin 3) ▷ _) := rfl
  rw [← Category.assoc _ _ (L).prism, hn, Category.assoc, (L).first]
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
  rw [TransportRepresentationFamilyWitness.leftPrism,
    ← Category.assoc (prismEndpoint 0 (leftUnstraightening F ⊗ (Δ[0] : SSet.{u + 1}))),
    prismEndpoint_associator_inv]
  let w := unstraighteningMappingFamilyWitness F G
    (SSet.const (coherentVertexOfHomotopy l) : (Δ[0] : SSet.{u + 1}) ⟶ _)
  change lift (𝟙 (leftUnstraightening F))
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
    (prismEndpoint 0 (leftUnstraightening F) ▷ (Δ[0] : SSet.{u + 1})) ≫ w.prism = _
  have hh := congrArg (fun z => lift (𝟙 (leftUnstraightening F))
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫ z) w.source
  simpa only [Category.assoc, ← Category.assoc _ (fst _ _), lift_fst,
    Category.id_comp] using hh

end SerrePositivity.InfinityCategories.F2
