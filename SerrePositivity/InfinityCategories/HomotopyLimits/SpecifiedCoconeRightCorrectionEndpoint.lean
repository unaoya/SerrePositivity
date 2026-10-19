module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightCorrectionHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionVertexEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.ContractibleEdgeEvaluation

/-!
概要：長辺の修正円柱を表す延長空間の辺が、終点で元の指定境界経路を保持することを示す。
方針：同じ円柱の頂点評価と、元の修正辺の fiber 制限を raw な一単体で照合する。
規約：単に両端が等しいという理由では類を同定しない。使われ方：共通長辺での高次照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanRightLeg

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "qC" => sliceUnderProjection (j ≫ p)
local notation "β" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "e" => partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "H" => specifiedCoconeRightCorrectionHomotopy hp p c hc dB dC
local notation "s" => specifiedCoconeRightCorrectionExtensionEdge hp p c hc dB dC
local notation "κ" => partialColimitSpecifiedCorrectionEdge hp p c hc dB dC
local notation "κE" => partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC
local notation "r" => normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)
local notation "rF" => normalizedCoconeRestrictionFiber (j ≫ p) g
  (coconePushoutBoundary_eq hp p) z

/-- 同じ根辺の全延長を元の終点で評価する射。 -/
def specifiedCoconeRightRootEndpoint :
    specifiedCoconeRightRootExtensionSpace hp p c hc dB dC ⟶ vertexFiber q z :=
  fixedExtensionEdgeTarget q β (stdSimplex.δ (1 : Fin 2)) v hv (𝟙 Δ[1]) e (Category.id_comp β)

/-- 元の修正辺を共通部分へ制限した同じ fiber 内の辺。 -/
def specifiedCoconeRightCommonCorrectionEdge := (κ).map rF

/-- 共通部分の修正辺の包含は、元の coslice の修正辺の同じ制限になる。 -/
lemma specifiedCoconeRightCommonCorrectionEdge_projection :
    SSet.yonedaEquiv.symm (specifiedCoconeRightCommonCorrectionEdge hp p c hc dB dC).edge ≫
        vertexFiberι q z = SSet.yonedaEquiv.symm (κE).edge ≫ r := by
  change SSet.yonedaEquiv.symm ((rF).app _ (κ).edge) ≫ vertexFiberι q z = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, normalizedCoconeRestrictionFiber,
    vertexFiberMap_ι]
  have hk : SSet.yonedaEquiv.symm (κ).edge ≫ vertexFiberι qC z =
      SSet.yonedaEquiv.symm (κE).edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t ↦ t ≫ r) hk)

/-- 延長空間の実際の修正辺の終点は、元の修正辺を raw な図式として回収する。 -/
lemma specifiedCoconeRightCorrectionExtensionEdge_endpoint_raw :
    SSet.yonedaEquiv.symm ((s).map
      (specifiedCoconeRightRootEndpoint hp p c hc dB dC)).edge ≫ vertexFiberι q z =
      SSet.yonedaEquiv.symm (κE).edge ≫ r := by
  have ht := fixedExtensionEdgeTarget_map_homotopy_raw q β (stdSimplex.δ (1 : Fin 2))
    v hv (𝟙 Δ[1]) e (Category.id_comp β)
    (specifiedCoconeRightCorrectionHomotopy_source_projection hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_source_initial hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC)
    H (specifiedCoconeRightCorrectionHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRightCorrectionHomotopy_initial hp p c hc dB dC)
  change _ = prismEndpoint 1 (Δ[1] : SSet.{u + 1}) ≫ (H).h at ht
  exact ht.trans (specifiedCoconeRightCorrectionHomotopy_target hp p c hc dB dC)

/-- 終点の一単体は、指定済みの修正辺の共通制限と厳密に一致する。 -/
lemma specifiedCoconeRightCorrectionExtensionEdge_endpoint_edge :
    ((s).map (specifiedCoconeRightRootEndpoint hp p c hc dB dC)).edge =
      (specifiedCoconeRightCommonCorrectionEdge hp p c hc dB dC).edge := by
  apply SSet.yonedaEquiv.symm.injective
  apply vertexFiber_hom_ext q z
  exact (specifiedCoconeRightCorrectionExtensionEdge_endpoint_raw hp p c hc dB dC).trans
    (specifiedCoconeRightCommonCorrectionEdge_projection hp p c hc dB dC).symm

/-- 同じ終点の類も、元の修正辺の共通制限の類そのものである。 -/
lemma specifiedCoconeRightCorrectionExtensionEdge_endpoint_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (((s).map (specifiedCoconeRightRootEndpoint hp p c hc dB dC)).toTruncated)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (specifiedCoconeRightCommonCorrectionEdge hp p c hc dB dC).toTruncated) :=
  SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (specifiedCoconeRightCorrectionExtensionEdge_endpoint_edge hp p c hc dB dC)

/-- 延長空間の同じ辺の終点は、元の指定境界経路の一単体そのものを保持する。 -/
lemma specifiedCoconeRightCorrectionExtensionEdge_boundary_edge :
    ((s).map (specifiedCoconeRightRootEndpoint hp p c hc dB dC)).edge =
      intervalFunctorVertexEdge (SSet.yonedaEquiv
        (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val :=
  (specifiedCoconeRightCorrectionExtensionEdge_endpoint_edge hp p c hc dB dC).trans
    (partialColimitSpecifiedCorrectionEdge_projection hp p c hc dB dC)

/-- 根辺の可縮な延長空間での正準比較の終点も、同じ指定修正辺の類を保つ。 -/
abbrev specifiedCoconeRightCorrectionExtensionEdge_canonical_hom_arrow :=
  contractibleEdgeEvaluation_hom_arrow
    (specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC)
    (specifiedCoconeRightRootEndpoint hp p c hc dB dC) s
    (SSet.Truncated.HomotopyCategory.homMk
      (specifiedCoconeRightCommonCorrectionEdge hp p c hc dB dC).toTruncated)
    (specifiedCoconeRightCorrectionExtensionEdge_endpoint_hom_arrow hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
