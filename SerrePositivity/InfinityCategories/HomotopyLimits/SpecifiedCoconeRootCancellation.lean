module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanBoundaryFactors
public import SerrePositivity.InfinityCategories.HomotopyLimits.ContractibleFactorCancellation
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeStandardRootComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeCorrectionClass

/-!
概要：共通根辺の左右・中央・指定修正の四因子を、元の境界同型の定義で相殺する。
方針：各因子の既存の点評価を使い、可縮な始域での正準比較を分解する。
規約：終点の一致だけから恒等を推論しない。使われ方：全 Hom 族の評価固定比較の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

private lemma comparison_endpoint_congr {X Y : SSet.{u}} (hX : IsContractibleKan X)
    (F : X ⟶ Y) {x x' y y' : X _⦋0⦌} (hx : x = x') (hy : y = y') :
    Arrow.mk (VertexIso.map (hX.vertexIso x y) F).hom =
      Arrow.mk (VertexIso.map (hX.vertexIso x' y') F).hom := by
  subst x' y'
  rfl

attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "β" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "S" => specifiedCoconeRightRootExtensionSpace hp p c hc dB dC
local notation "hS" => specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC
local notation "F" => specifiedCoconeRightRootEndpoint hp p c hc dB dC
local notation "uL" => NatTrans.app (specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC) _
  (specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC)
local notation "sL" => NatTrans.app (specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC) _
  (specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC)
local notation "uR" => NatTrans.app
  (specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC) _
  (specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC)
local notation "sR" => NatTrans.app
  (specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC) _
  (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC)
local notation "L" => partialColimitSpanLeftBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "M" => partialColimitSpanMiddleBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "R" => partialColimitSpanRightBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "K" => partialColimitSpanBoundaryIso c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "v₀" => initialFiberVertexAt q c (JoinCocone.vertex c) rfl
local notation "eB" => partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "ε" => Iso.hom (pointFunctorEvaluationIso (vertexFiber q z))

/-- 左因子の終点は、同じ結合順序に揃えた境界・付加輸送の評価である。 -/
abbrev specifiedCoconeRootLeftFactor_hom_arrow :=
  (specifiedCoconeLeftCommonRootComparisonIso_boundary_hom_arrow hp p c hc dB dC).trans
    (vertexIso_map_hom_arrow ε
      (partialColimitSpanLeftBoundaryFactor_hom_arrow c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).symm

/-- 中央因子の終点は、元の native 比較の同じ一点制限の評価である。 -/
abbrev specifiedCoconeRootMiddleFactor_hom_arrow :=
  (specifiedCoconeStandardRootComparisonIso_endpoint_hom_arrow hp p c hc dB dC).trans
    (functorIsoComponent_point_hom_arrow
      (partialColimitSpanTransportIso c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC q) v₀)

/-- 右因子の終点も、同じ結合順序に揃えた境界・付加輸送の評価である。 -/
abbrev specifiedCoconeRootRightFactor_hom_arrow :=
  (specifiedCoconeRightPrefixCommonRootComparisonIso_boundary_hom_arrow hp p c hc dB dC).trans
    (vertexIso_map_hom_arrow ε
      (partialColimitSpanRightBoundaryFactor_hom_arrow c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).symm

/-- 同じ指定四面体の修正後の長辺を、同じ共通根辺の空間の頂点として保持する。 -/
def specifiedCoconeCorrectedRootVertex : (S) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv q β a v hv
    ⟨tetrahedronRootEdge ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC,
      specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC,
      specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC⟩

/-- 右の実際の長辺から同じ修正後長辺への比較は、元の指定境界同型を評価する。 -/
lemma specifiedCoconeRootCorrectionFactor_hom_arrow :
    Arrow.mk (VertexIso.map ((hS).vertexIso uR
      (specifiedCoconeCorrectedRootVertex hp p c hc dB dC)) F).hom =
      Arrow.mk (VertexIso.map K ε).hom := by
  have h := comparison_endpoint_congr hS F
    (specifiedCoconeRightPrefixCommonRootRestriction_actual hp p c hc dB dC)
    (show specifiedCoconeCorrectedRootVertex hp p c hc dB dC = _ from rfl)
  exact h.trans (specifiedCoconeCorrectionCanonical_boundary_hom_arrow hp p c hc dB dC)

/-- 元の左長辺から同じ指定修正後の右長辺への、共通根辺内の正準比較。 -/
def specifiedCoconeRootClosingComparisonIso :=
  (hS).vertexIso uL (specifiedCoconeCorrectedRootVertex hp p c hc dB dC)

/-- 元の指定境界同型が四因子を相殺するので、この比較の終点の類は恒等射である。 -/
lemma specifiedCoconeRootClosingComparisonIso_endpoint_hom_arrow :
    Arrow.mk (VertexIso.map (specifiedCoconeRootClosingComparisonIso hp p c hc dB dC) F).hom =
      Arrow.mk (𝟙 (Arrow.mk (VertexIso.map L ε).hom).left) := by
  have hK := congrArg (fun I ↦ VertexIso.map I ε)
    (partialColimitSpanBoundaryIso_factors c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
  have hInv := hK.trans (vertexIso_map_inverse_threeFactors L M R ε)
  have hCorrection := (specifiedCoconeRootCorrectionFactor_hom_arrow hp p c hc dB dC).trans
    (congrArg (fun I ↦ Arrow.mk I.hom) hInv)
  exact contractibleVertexIso_endpoint_cancel hS F uL sL sR uR
    (specifiedCoconeCorrectedRootVertex hp p c hc dB dC)
    (VertexIso.map L ε) (VertexIso.map M ε) (VertexIso.map R ε)
    (specifiedCoconeRootLeftFactor_hom_arrow hp p c hc dB dC)
    (specifiedCoconeRootMiddleFactor_hom_arrow hp p c hc dB dC)
    (specifiedCoconeRootRightFactor_hom_arrow hp p c hc dB dC) hCorrection

end
end SerrePositivity.InfinityCategories.HomotopyLimits
