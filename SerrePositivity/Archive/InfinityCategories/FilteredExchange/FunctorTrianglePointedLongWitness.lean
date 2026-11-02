module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTrianglePointedLift
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningTriangleRelativeRestriction

/-!
概要：全底上に戻した元の指定三角形の長辺を、既存の指定比較の同じ証拠へ同定する。
方針：元の全三角形の長辺公式を制限し、元の相対頂点比較の制限式を適用する。
規約：長辺・prism・同型の値を保持。使われ方：第零面の全族比較から指定合成比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (s : C ⟶ leftUnstraightening F)
local notation "V" => coherentTriangleOfFunctorTriangle T
local notation "w" => unstraighteningMappingTriangleLongWitness F G J
  (SSet.const (coherentVertexOfHomotopy l)) (SSet.const (coherentVertexOfHomotopy r))
  (SSet.const (coherentVertexOfHomotopy d))
  (CoherentTransformationVertexTriangle.diagram (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.first (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.second (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.long (coherentTriangleOfFunctorTriangle T))

/-- 元の全三角形の長辺は、既存の指定比較に用いた同じ元の長辺証拠の実制限。 -/
lemma functorTrianglePointedLift_long :
    (Δ[1] ◁ s) ≫ (stdSimplex.δ (1 : Fin 3) ▷ leftUnstraightening F) ≫
      functorTrianglePointedLift T =
    prismParameterRestriction (lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
      (w).prism := by
  have hl := coherentTransformationTriangleLift_long F G J (coherentVertexOfHomotopy l)
    (coherentVertexOfHomotopy r) (coherentTriangleOfFunctorTriangle T)
  change (w).prism = _ at hl
  rw [prismParameterRestriction, hl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [functorTrianglePointedLift]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の相対三角形比較は、同じ全長辺証拠の指定終点比較へ値を変えずに戻る。 -/
lemma functorTrianglePointedLift_comparison_pre :
    HEq
      (VertexIso.map (unstraighteningTriangleRelativeVertexIso F G J
        (coherentVertexOfHomotopy l) (coherentVertexOfHomotopy r) (coherentVertexOfHomotopy d)
        (V).diagram (V).first (V).second (V).long)
        (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s))
      (unstraighteningIdentityRestrictedEndpointIso F J (SSet.const (coherentVertexOfHomotopy d))
        (w).prism (w).source (w).projection (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) s) :=
  unstraighteningTriangleRelativeVertexIso_pre F G J (coherentVertexOfHomotopy l)
    (coherentVertexOfHomotopy r) (coherentVertexOfHomotopy d)
    (V).diagram (V).first (V).second (V).long s

end SerrePositivity.InfinityCategories.F2
