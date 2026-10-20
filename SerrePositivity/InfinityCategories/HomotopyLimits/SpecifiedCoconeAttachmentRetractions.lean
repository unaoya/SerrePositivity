module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftAttachmentFace
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightAttachmentFace
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.InitialEdgeFamilyRetractionProjection
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyEndpointTransport

/-!
概要：元の根辺三角形・四面体の初期族を、実際の付加辺による枝終点の前置像へ結ぶ。
方針：同じ付加辺面の相対円柱を制限し、両端の厳密な式だけで表示変更する。
規約：底の元の円柱と全時刻の共通評価を保持。使われ方：共通 end の全経路の貼り合わせ。
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
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y

section
local notation "e" => colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "L" => specifiedCoconeLeftAttachmentFaceFamily hp p c hc dB dC y
local notation "hL" => specifiedCoconeLeftAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "K" => (L ≫ sliceUnderRestrict t (stdSimplex.δ (0 : Fin 2))) ≫
  relativeEdgeCosliceSection t q
local notation "hK" => initialEdgeFamilyRetraction_section_fixed q t y L hL
local notation "Φ" => colimitAttachmentTotalPrecomposition c hc f (i ≫ p) rfl dB y
local notation "IB" => specifiedCoconeLeftBranchInitialHomFamily hp p c hc dB dC y
local notation "J" => initialDiagramHomFamily q _ t (stdSimplex.δ (0 : Fin 2))
  (SSet.Edge.δ_zero_yonedaEquiv_symm e) y L hL

/-- 元の左枝終点の前置像は、同じ付加辺面の終端を普遍相対切断で戻した初期族。 -/
lemma specifiedCoconeLeftAttachmentPrecomposition : IB ≫ Φ =
    initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
      (SSet.Edge.δ_one_yonedaEquiv_symm e) y K hK := by
  calc
    _ = specifiedCoconeLeftBranchCommonInitialFamily hp p c hc dB dC y ≫
        initialTotalEdgePrecomposition q e y := (Category.assoc _ _ _).symm
    _ = J ≫ initialTotalEdgePrecomposition q e y :=
      congrArg (· ≫ initialTotalEdgePrecomposition q e y)
        (specifiedCoconeLeftAttachmentFaceFamily_target hp p c hc dB dC y).symm
    _ = _ := initialTotalEdgePrecomposition_family q e y L hL

/-- 元の左根辺初期族から枝終点の前置像へ、同じ底の円柱を保って結ぶ。 -/
def specifiedCoconeLeftAttachmentInitialHomotopy : SSet.Homotopy
    (specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y) (IB ≫ Φ) :=
  homotopyEndpointTransport
    (initialEdgeFamilyRetraction q c t (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL)
    (specifiedCoconeLeftAttachmentFaceFamily_source hp p c hc dB dC y)
    (specifiedCoconeLeftAttachmentPrecomposition hp p c hc dB dC y).symm

/-- 両端の表示変更後も、元の同じ付加辺面の比較円柱を保持する。 -/
lemma specifiedCoconeLeftAttachmentInitialHomotopy_raw :
    (specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y).h =
      (initialEdgeFamilyRetraction q c t (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL).h :=
  homotopyEndpointTransport_raw _ _ _

/-- 比較の全時刻で、元の同じ共通 Hom 族を厳密に評価する。 -/
lemma specifiedCoconeLeftAttachmentInitialHomotopy_evaluation :
    (specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialEvaluation q c y = fst _ Δ[1] ≫ V := by
  rw [specifiedCoconeLeftAttachmentInitialHomotopy_raw, initialEdgeFamilyRetraction_evaluation]
  have hv := initialDiagramHomFamily_evaluation q c t (stdSimplex.δ (1 : Fin 2))
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL
  rw [specifiedCoconeLeftAttachmentFaceFamily_source,
    specifiedCoconeLeftInitialHomFamily_evaluation] at hv
  exact congrArg (fst _ Δ[1] ≫ ·) hv.symm

/-- 底は、元の同じ付加辺面の底の切断比較を始点へ制限した円柱そのもの。 -/
lemma specifiedCoconeLeftAttachmentInitialHomotopy_projection :
    (specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialProjection q c y =
      (cosliceEdgeFamilyPrecompositionCylinder (t ≫ q) y
        (relativeEdgeFamilyBase t q L y hL) (SSet.yonedaEquiv.symm c ≫ q)
        (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q)) (initialTotalEdgeBase_source q e) rfl).h := by
  rw [specifiedCoconeLeftAttachmentInitialHomotopy_raw]
  exact initialEdgeFamilyRetraction_baseCylinder q c t
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL
end

section
local notation "e" => colimitAttachmentRestrictionEdge c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "L" => specifiedCoconeRightAttachmentFaceFamily hp p c hc dB dC y
local notation "hL" => specifiedCoconeRightAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "K" => (L ≫ sliceUnderRestrict t (stdSimplex.δ (0 : Fin 2))) ≫
  relativeEdgeCosliceSection t q
local notation "hK" => initialEdgeFamilyRetraction_section_fixed q t y L hL
local notation "Φ" => colimitAttachmentTotalPrecomposition c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC y
local notation "IB" => specifiedCoconeRightBranchInitialHomFamily hp p c hc dB dC y
local notation "J" => initialDiagramHomFamily q _ t (stdSimplex.δ (0 : Fin 2))
  (SSet.Edge.δ_zero_yonedaEquiv_symm e) y L hL

/-- 元の右枝終点の前置像は、同じ付加辺面の終端を普遍相対切断で戻した初期族。 -/
lemma specifiedCoconeRightAttachmentPrecomposition : IB ≫ Φ =
    initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
      (SSet.Edge.δ_one_yonedaEquiv_symm e) y K hK := by
  calc
    _ = specifiedCoconeRightBranchCommonInitialFamily hp p c hc dB dC y ≫
        initialTotalEdgePrecomposition q e y := (Category.assoc _ _ _).symm
    _ = J ≫ initialTotalEdgePrecomposition q e y :=
      congrArg (· ≫ initialTotalEdgePrecomposition q e y)
        (specifiedCoconeRightAttachmentFaceFamily_target hp p c hc dB dC y).symm
    _ = _ := initialTotalEdgePrecomposition_family q e y L hL

/-- 元の右根辺初期族から枝終点の前置像へ、同じ底の円柱を保って結ぶ。 -/
def specifiedCoconeRightAttachmentInitialHomotopy : SSet.Homotopy
    (specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y) (IB ≫ Φ) :=
  homotopyEndpointTransport
    (initialEdgeFamilyRetraction q c t (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL)
    (specifiedCoconeRightAttachmentFaceFamily_source hp p c hc dB dC y)
    (specifiedCoconeRightAttachmentPrecomposition hp p c hc dB dC y).symm

/-- 両端の表示変更後も、元の同じ付加辺面の比較円柱を保持する。 -/
lemma specifiedCoconeRightAttachmentInitialHomotopy_raw :
    (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y).h =
      (initialEdgeFamilyRetraction q c t (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL).h :=
  homotopyEndpointTransport_raw _ _ _

/-- 比較の全時刻で、元の同じ共通 Hom 族を厳密に評価する。 -/
lemma specifiedCoconeRightAttachmentInitialHomotopy_evaluation :
    (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialEvaluation q c y = fst _ Δ[1] ≫ V := by
  rw [specifiedCoconeRightAttachmentInitialHomotopy_raw, initialEdgeFamilyRetraction_evaluation]
  have hv := initialDiagramHomFamily_evaluation q c t (stdSimplex.δ (1 : Fin 2))
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL
  rw [specifiedCoconeRightAttachmentFaceFamily_source,
    specifiedCoconeRootedInitialHomFamily_evaluation] at hv
  exact congrArg (fst _ Δ[1] ≫ ·) hv.symm

/-- 底は、元の同じ付加辺面の底の切断比較を始点へ制限した円柱そのもの。 -/
lemma specifiedCoconeRightAttachmentInitialHomotopy_projection :
    (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialProjection q c y =
      (cosliceEdgeFamilyPrecompositionCylinder (t ≫ q) y
        (relativeEdgeFamilyBase t q L y hL) (SSet.yonedaEquiv.symm c ≫ q)
        (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q)) (initialTotalEdgeBase_source q e) rfl).h := by
  rw [specifiedCoconeRightAttachmentInitialHomotopy_raw]
  exact initialEdgeFamilyRetraction_baseCylinder q c t
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
