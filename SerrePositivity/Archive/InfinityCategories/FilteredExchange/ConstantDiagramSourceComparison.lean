module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningSourceActualWitnessComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantDiagramWitnessCurryComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：元の始域恒等射付き定値図式比較の fiber 像を、同じ二実輸送の比較へ戻す。
方針：同じ普遍証拠の終点比較へ戻し、定値 fiber と curry の整合を合成する。
規約：元の指定比較と全係数を保持。使われ方：長辺比較の下側輸送因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
  (a : K ⟶ intervalMappingSpace x y)
local notation "F" => (SSet.const x : B ⟶ SpaceInfinity)
local notation "G" => (SSet.const y : B ⟶ SpaceInfinity)
local notation "E" => leftUnstraightening F
local notation "q" => leftUnstraighteningProjection F
local notation "t" => constantDiagramTransformation B a
local notation "d" => ((Δ[1] ◁ q) ▷ K) ≫ functorParameterizedPrism (intervalMappingUncurry t)
local notation "i" => prismEndpoint 0 E ▷ K
local notation "j" => prismEndpoint 1 E ▷ K
local notation "hi" => leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne E) K
local notation "v" => fst E K ≫ pullback.fst pointedSpaceProjection F
local notation "g" => relativeFunctorUncurry (t ≫ leftUnstraighteningMappingSpaceMap F G)
local notation "w" => unstraighteningMappingFamilyWitness F G t
local notation "hv" => unstraighteningMappingFamilyWitness_initial_base F G t
local notation "hj" => unstraighteningMappingFamilyWitness_final_base F G t

/-- 元の始域付き比較の定値 fiber 像は、同じ二輸送の endpointIso の全 curry。 -/
lemma constantDiagramSourceComparison_heq_transport
    (f : E ⊗ K ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = fst E K ≫ q)
    (W : UnstraighteningFamilyWitness F G t f) :
    HEq ((unstraighteningSourceFamilyComparisonIso F G q (𝟙 E) (Category.id_comp _)
      t f hf W.prism W.source W.target W.projection).postcomp
        (constantUnstraighteningRelativeIso q y).hom)
      (VertexIso.map ((constantDiagramTransportWitness w).endpointIso pointedSpaceProjection
        (constantUnstraighteningFiberProjection B x) (intervalMappingUncurry a)
        (intervalMappingUncurry_one a) (constantDiagramTransportWitness W))
        (functorSpaceCurryMap E K (vertexFiber pointedSpaceProjection y))) := by
  let e := relativeFunctorExtensionEndpoint_curryIso pointedSpaceProjection d i hi v hv
    j G q hj (UnstraighteningFamilyWitness.prism w) W.prism
    (UnstraighteningFamilyWitness.projection w) W.projection
    (UnstraighteningFamilyWitness.source w) W.source g f
    (relativeFunctorUncurry_projection _) hf (UnstraighteningFamilyWitness.target w) W.target
  have h := unstraighteningSourceComparisonIso_heq_actualWitness F G t f hf W
  have hs : relativeFunctorCurry g (relativeFunctorUncurry_projection _) =
      (t ≫ leftUnstraighteningMappingSpaceMap F G) ≫
        relativeFunctorOverPre (leftUnstraighteningProjection G)
          (Over.homMk (U := Over.mk q) (V := Over.mk q) (𝟙 E) (Category.id_comp _)) := by
    apply relativeFunctorUncurry_injective
    rw [relativeFunctorUncurry_curry]
    have hh := relativeFunctorOverPre_uncurry (leftUnstraighteningProjection G)
      (Over.homMk (U := Over.mk q) (V := Over.mk q) (𝟙 E) (Category.id_comp _))
      (t ≫ leftUnstraighteningMappingSpaceMap F G)
    exact (hh.trans (by apply SSet.hom_ext; intro n; rfl)).symm
  refine (functorIso_postcomp_heq_of_heq e _ hs rfl h
    (constantUnstraighteningRelativeIso q y).hom).trans ?_
  exact constantDiagramWitnessCurryComparison_heq_transport a g f
    (relativeFunctorUncurry_projection _) hf w W hv hj

end SerrePositivity.InfinityCategories.F2
