module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportPointEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantDiagramTransportMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantDiagramTransportComparisonValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport

/-!
概要：元の定値余極限区間の輸送比較を、元の実長辺作用上の同じ一点比較へ戻す。
方針：元の比較の始域等式と同じ普遍証拠の値の一致を使う。
規約：元の比較を保持。使われ方：元の下側因子の輸送比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (c : SSet.Homotopy F J)
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "C" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B c))
local notation "C₀" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B c)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)

/-- 元の定値輸送比較の同じ一点始域は、元の長辺作用の同じ fiber 射影。 -/
lemma coherentColimitConstantTransport_source_point :
    s ≫ uncurry ((constantDiagramTransformation ((SSet.uliftFunctor.{u + 1, u}).obj B) C₀ ≫
      leftUnstraighteningMappingSpaceMap (SSet.const z₀) (SSet.const z₃)) ≫
        (constantUnstraighteningRelativeIso (leftUnstraighteningProjection
          (SSet.const z₀ : ((SSet.uliftFunctor.{u + 1, u}).obj B) ⟶ SpaceInfinity)) z₃).hom) =
      (leftUnstraighteningMappingVertexMap _ _ C).val ≫
        constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃ := by
  exact (congrArg (fun h => s ≫ h) (constantDiagramMappingTransportIso_source C₀)).trans
    (coherentColimitConstantTransport_endpoint_point B l)

/-- 元の区間の定値輸送比較の一点成分を、元の実長辺作用を始域として保持する。 -/
def coherentColimitConstantTransportPointIso :=
  functorIsoOfEq
    ((constantDiagramMappingTransportIso ((SSet.uliftFunctor.{u + 1, u}).obj B) C₀).precomp s)
    (coherentColimitConstantTransport_source_point B c) rfl

/-- 元の一点比較は、同じ普遍実輸送の同じ一点比較と厳密に同じ指定値。 -/
lemma coherentColimitConstantTransportPointIso_eq_witness :
    coherentColimitConstantTransportPointIso B c =
      functorIsoOfEq ((pointedIntervalTransportComparison
        (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₀) C₀
        (constantDiagramTransportWitness
          (constantDiagramMappingFamilyWitness
            ((SSet.uliftFunctor.{u + 1, u}).obj B) C₀))).precomp s)
        (coherentColimitConstantTransport_endpoint_point B l) rfl := by
  refine eq_of_heq ((functorIsoOfEq_heq _ _ _).trans ?_)
  refine (functorIso_precomp_heq_of_heq _ _
    (constantDiagramMappingTransportIso_source C₀).symm rfl
    (constantDiagramMappingTransportIso_heq_witness
      ((SSet.uliftFunctor.{u + 1, u}).obj B) C₀) s).trans ?_
  exact (functorIsoOfEq_heq _ _ _).symm

end SerrePositivity.InfinityCategories.F2
