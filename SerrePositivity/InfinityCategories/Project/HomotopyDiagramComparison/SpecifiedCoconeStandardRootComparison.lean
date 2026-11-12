module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeCommonRootComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.StandardLongComparison

/-!
概要：共通根辺上の二つの標準長辺を、元の二単体による同じ点輸送へ同定する。
方針：長辺制限と底の移送が保持した実際の図式を、標準 prism の点評価と照合する。
規約：同じ根辺空間の正準比較を使う。使われ方：元の指定境界経路の中心因子。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma pointTriangle_long {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
    (σ : SSet.Edge.CompStruct e f g) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism p σ) v := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation_shape]
  rfl

private lemma contractibleComparison_endpoint_congr {X Y : SSet.{u}}
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X) (F : X ⟶ Y) {x x' y y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x y) F).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x' y') F).hom := by
  subst x' y'
  rfl

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "β" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "v" => SSet.yonedaEquiv.symm c
local notation "k" => stdSimplex.δ (1 : Fin 3)
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "σL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "σR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "βL" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σL)
local notation "βR" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σR)
local notation "hvL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial_base hp p c hc dB dC
local notation "hvR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtension_initial_base hp p c hc dB dC
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace hp p c hc dB dC

local notation "v₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex c) rfl
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint hp p c hc dB dC

/-- 同じ標準三角形の共通根辺への像は、元の長辺 prism の点評価そのもの。 -/
lemma specifiedCoconeLeftCommonRootRestriction_standard :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportLongPointExtensionVertex q v₀ σL := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex q σL v₀
  have h₁ := congrArg
    (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso q
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)
      a v ((hvL).trans (Category.assoc _ _ _)) hv).hom.app _ z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftStandardTriangleExtensionVertex_long hp p c hc dB dC)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso_vertex q
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)
    a v ((hvL).trans (Category.assoc _ _ _)) hv (k ≫ T)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ k ≫ z)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection q σL v₀)))
    ((Category.assoc _ _ _).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftStandardTriangleExtension_initial hp p c hc dB dC))
  refine h₁.trans (h₂.trans ?_)
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q β a v hv)
  apply Subtype.ext
  exact pointTriangle_long q σL v₀

/-- 同じ標準三角形の共通根辺への像は、元の長辺 prism の点評価そのもの。 -/
lemma specifiedCoconeRightPrefixCommonRootRestriction_standard :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportLongPointExtensionVertex q v₀ σR := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex q σR v₀
  have h₁ := congrArg
    (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso q
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)
      a v ((hvR).trans (Category.assoc _ _ _)) hv).hom.app _ z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixStandardTriangleExtensionVertex_long hp p c hc dB dC)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso_vertex q
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)
    a v ((hvR).trans (Category.assoc _ _ _)) hv (k ≫ T)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ k ≫ z)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection q σR v₀)))
    ((Category.assoc _ _ _).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixStandardTriangleExtension_initial hp p c hc dB dC))
  refine h₁.trans (h₂.trans ?_)
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q β a v hv)
  apply Subtype.ext
  exact pointTriangle_long q σR v₀

/-- 元の共通根辺上の二つの標準長辺の正準比較。 -/
def specifiedCoconeStandardRootComparisonIso :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC).vertexIso
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC))
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC))

/-- 標準長辺間の同じ正準比較の終点は、元の native な span 合成同型の同じ成分。 -/
lemma specifiedCoconeStandardRootComparisonIso_endpoint_hom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (specifiedCoconeStandardRootComparisonIso hp p c hc dB dC) F).hom =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportIso c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC q).toNatIso.hom.app
          (SSet.HomotopyCategory.mk v₀)) := by
  have h := contractibleComparison_endpoint_congr
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC) F
    (specifiedCoconeLeftCommonRootRestriction_standard hp p c hc dB dC)
    (specifiedCoconeRightPrefixCommonRootRestriction_standard hp p c hc dB dC)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportStandardLongComparisonIso_endpoint_hom_arrow q v₀ σL σR)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
