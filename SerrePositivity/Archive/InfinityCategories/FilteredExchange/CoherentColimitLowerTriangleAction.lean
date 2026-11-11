module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerCompositeVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerTransportVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleConstantTargetValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：下面の指定族比較の値への像を、同じ下面の全空間作用の比較へ移す。
方針：元の両端と比較値を揃え、同じ相対 Hom の値への作用で写す。
規約：下面・指定区間・対角を保持。使われ方：上下面の共役因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "T" => coherentColimitTargetLowerTriangle B H
local notation "z" => coherentDiagramTotalVertex G
local notation "v" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "q" => Iso.hom (constantUnstraighteningRelativeIso
  (leftUnstraighteningProjection F) z)
local notation "m" => CategoryTheory.Functor.map (ihom (leftUnstraightening F))
  (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))

/-- 元の下面の全空間作用の比較を、そのまま元の値への後合成で写す。 -/
def coherentColimitLowerTriangleActionIso :
    FunctorIso (coherentColimitLowerAction B H) (coherentColimitLowerCompositeAction B H) :=
  FunctorIso.postcomp
    (unstraighteningTriangleVertexIso F
      (SSet.const (coherentDiagramTotalCocone F).vertex) (SSet.const z)
      (coherentVertexOfHomotopy (coconeTransformationHomotopy (coherentDiagramTotalCocone F)))
      (coherentVertexOfHomotopy (coherentColimitIntervalConstantHomotopy B H))
      (coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H))
      (coherentTriangleOfFunctorTriangle T).diagram (coherentTriangleOfFunctorTriangle T).first
      (coherentTriangleOfFunctorTriangle T).second (coherentTriangleOfFunctorTriangle T).long)
    (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z ≫
      (pointedSpaceFiberValueEquivalence z).hom)

/-- 下面の指定区間族比較の像は、元の全下面の全空間作用比較と同じ指定値を持つ。 -/
lemma coherentColimitLowerCompositeIso_map_heq_action :
    HEq (VertexIso.map ((coherentColimitLowerCompositeIso B H).app v) (q ≫ m))
      (coherentColimitLowerTriangleActionIso B H) := by
  have h := vertexIso_map_heq_of_heq ((coherentColimitLowerCompositeIso B H).app v)
    (functorTriangleRelativeComparison T)
    (coherentColimitLowerComposite_source_vertex B H)
    (coherentColimitLowerComposite_target_vertex B H)
    (coherentColimitLowerCompositeIso_app_heq_triangle B H) (q ≫ m)
  exact h.trans (functorTriangleRelativeComparison_map_constantTarget T)

end SerrePositivity.InfinityCategories.F2
