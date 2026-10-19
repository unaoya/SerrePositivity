module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootCancellation

/-!
概要：元の左右の長辺を結ぶ底・始点固定円柱を保持し、その終点の類の相殺を回収する。
方針：同じ共通根辺の延長を結ぶ円柱を選び、同じ可縮な空間の辺へ戻す。
規約：終点はまだ全時刻固定とは主張しない。使われ方：終点固定の全 Hom 比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
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
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫
  specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "V" => tetrahedronRootEdge ≫
  specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "S" => specifiedCoconeRightRootExtensionSpace hp p c hc dB dC
local notation "hS" => specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC
local notation "F" => specifiedCoconeRightRootEndpoint hp p c hc dB dC
local notation "L" => partialColimitSpanLeftBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "ε" => Iso.hom (pointFunctorEvaluationIso (vertexFiber q z))

/-- 閉じる円柱の元の左長辺も、同じ共通余錐を始点とする。 -/
lemma specifiedCoconeRootClosingLeft_initial : a ≫ W = v :=
  (Category.assoc _ _ _).symm.trans
    (specifiedCoconeLeftTriangleExtension_initial hp p c hc dB dC)

local notation "hW" => specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC
local notation "hV" => specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC
local notation "hWi" => specifiedCoconeRootClosingLeft_initial hp p c hc dB dC
local notation "hVi" => specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC

/-- 元の左長辺から同じ指定修正後の右長辺へ向かう、底・始点固定の実際の円柱。 -/
def specifiedCoconeRootClosingHomotopy : SSet.Homotopy W V :=
  (exists_homotopy_over_fixed_extension q β a edgeInitial_leftAnodyne v hv
    W V hW hV hWi hVi).choose

/-- 同じ元の共通根辺の底を全時刻で固定する。 -/
lemma specifiedCoconeRootClosingHomotopy_projection :
    (specifiedCoconeRootClosingHomotopy hp p c hc dB dC).h ≫ q =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ β :=
  (exists_homotopy_over_fixed_extension q β a edgeInitial_leftAnodyne v hv
    W V hW hV hWi hVi).choose_spec.1

/-- 始点も同じ元の共通余錐のまま、全時刻で固定する。 -/
lemma specifiedCoconeRootClosingHomotopy_initial :
    (a ▷ (Δ[1] : SSet.{u + 1})) ≫
        (specifiedCoconeRootClosingHomotopy hp p c hc dB dC).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ v :=
  (exists_homotopy_over_fixed_extension q β a edgeInitial_leftAnodyne v hv
    W V hW hV hWi hVi).choose_spec.2

/-- 同じ閉じる円柱を、共通根辺の延長空間の実際の辺として保持する。 -/
def specifiedCoconeRootClosingExtensionEdge :=
  fixedExtensionHomotopyEdge q β a v hv hW hV hWi hVi
    (specifiedCoconeRootClosingHomotopy hp p c hc dB dC)
    (specifiedCoconeRootClosingHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRootClosingHomotopy_initial hp p c hc dB dC)

/-- 展開すると同じ実際の閉じる円柱を回収する。 -/
lemma specifiedCoconeRootClosingExtensionEdge_uncurry :
    relativeFunctorUncurry (SSet.yonedaEquiv.symm
      (specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC).edge ≫
        relativeFunctorExtensionSpaceι q β a v hv) =
      (specifiedCoconeRootClosingHomotopy hp p c hc dB dC).h :=
  fixedExtensionHomotopyEdge_uncurry _ _ _ _ _ _ _ _ _ _ _ _

/-- 同じ実際の円柱の終点の辺の類も、四因子の相殺によって恒等射である。 -/
lemma specifiedCoconeRootClosingExtensionEdge_endpoint_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      ((specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC).map F).toTruncated) =
      Arrow.mk (𝟙 (Arrow.mk (VertexIso.map L ε).hom).left) := by
  have hE := contractibleEdgeEvaluation_hom hS F
    (specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC)
  have hC := comparison_endpoint_congr hS F
    (specifiedCoconeLeftCommonRootRestriction_actual hp p c hc dB dC).symm
    (show specifiedCoconeCorrectedRootVertex hp p c hc dB dC = _ from rfl)
  exact (congrArg Arrow.mk hE).trans (hC.trans
    (specifiedCoconeRootClosingComparisonIso_endpoint_hom_arrow hp p c hc dB dC))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
