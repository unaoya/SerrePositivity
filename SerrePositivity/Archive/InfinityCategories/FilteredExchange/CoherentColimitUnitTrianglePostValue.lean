module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoChainTransport

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeUnitValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleConstantPostValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyConstantPostTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport

/-!
概要：元の単位作用後の全三角形比較の値を、同じ native 単位表現の値へ戻す。
方針：同じ実円柱の標的表示を移し、元の全空間比較の後合成を回収する。
規約：元の三角形・単位円柱・指定値を保持。使われ方：上側の単位因子の交換則への接続。
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
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "u₀" => coconeTransformationHomotopy (coherentDiagramTotalCocone J)
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "Q" => Iso.hom (constantUnstraighteningRelativeIso p z₀) ≫
  CategoryTheory.Functor.map (ihom (leftUnstraightening F))
    (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z₀))

/-- 元の整合式の単位作用後の因子は、同じ全三角形の native 単位値への後合成に一致。 -/
lemma coherentColimitUnitTrianglePostValue_heq_native :
    HEq (VertexIso.map (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x₀)
      (functorHomotopyRelativePost u₀ p)) Q)
      ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J)) := by
  refine (functorHomotopyConstantPost_value_heq_target u₀ (coherentNativeUnitHomotopy J)
    (coherentDiagramTotalCocone_vertex J) (coherentNativeUnitHomotopy_h J).symm p
    ((functorTriangleSequentialPostComparison T p).app x₀)).trans ?_
  refine (functorTriangleSequentialPostComparison_map_constantPost T
    (coherentNativeUnitHomotopy J)).trans ?_
  have hv : (leftUnstraighteningMappingVertexMap J (SSet.const (coherentDiagramTotalVertex J))
      (coherentVertexOfHomotopy (coherentNativeUnitHomotopy J))).val ≫
        constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B)
          (coherentDiagramTotalVertex J) ≫
            (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex J)).hom =
        coherentNativeUnitValueAction J := by
    unfold coherentNativeUnitValueAction
    rw [coherentNativeUnitHomotopy, coherentVertexOfHomotopy_of_vertex]
  exact (functorIso_postcomp_heq_of_map_eq (functorTriangleTotalActionIso T) hv).symm

end SerrePositivity.InfinityCategories.F2
