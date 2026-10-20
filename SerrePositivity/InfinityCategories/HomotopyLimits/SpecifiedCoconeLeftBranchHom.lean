module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftHomTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointRestrictionFullHomCylinder

/-!
概要：元の左枝の全辺族から、同じ実際の左脚への評価固定 Hom 比較を構成する。
方針：枝の初期制限を評価固定で始対象の切断へ結び、底の同じ前合成へ射影する。
規約：標準 prism 自身の左辺と全 Hom の族を保持。使われ方：共通根辺との比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB) (dC : JoinCocone (j ≫ p))
  (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (i ≫ p)
local notation "r" => sliceUnderRestrict p i
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "k" => specifiedCoconeLeftTransportEdge hp p c hc dB dC
local notation "U" => coconePointHomFamily d y ≫ cosliceRestrictionFiberMap p i y
local notation "e" => coconeRestrictionEdgeApex i dB d k
local notation "P" => leftFibrationInitialProjection q dB y ≫
  Iso.hom (leftFibrationInitialBaseIso q dB y)

/-- 元の左脚の前合成は、同じ枝の初期 Hom の底の前合成そのもの。 -/
lemma specifiedCoconeLeftBranchPrecomposition_eq :
    initialRestrictionHomPrecomposition (sliceUnderProjection p) q r
        (sliceUnderRestrict_projection p i) d k y = coconeApexHomPrecomposition dB d e y :=
  coconeBranchHomPrecomposition_eq dB d e y i rfl k rfl

/-- 元の左全辺族を、枝の始対象 dB の初期 Hom 空間へ移す。 -/
def specifiedCoconeLeftBranchInitialHomFamily :
    pinchedHomLeft (JoinCocone.vertex d) y ⟶ leftFibrationInitialTotal q dB y :=
  pointRestrictionInitialHomFamily (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p i) d k y
local notation "I" => specifiedCoconeLeftBranchInitialHomFamily hp p c hc dB dC y

/-- 初期 Hom の包含後は、元の左全辺族の同じ初期頂点制限である。 -/
lemma specifiedCoconeLeftBranchInitialHomFamily_ι :
    I ≫ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm dB) ≫ q) y =
      specifiedCoconeLeftFullHomFamily hp p c hc dB dC y ≫ normalizedCoconeRestriction
        (SSet.yonedaEquiv.symm (k).edge) (stdSimplex.δ (1 : Fin 2))
        (SSet.Edge.δ_one_yonedaEquiv_symm k) :=
  pointRestrictionInitialHomFamily_ι (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p i) d k y

/-- 中間族の評価は、元の全 Hom 族の左枝への制限そのもの。 -/
lemma specifiedCoconeLeftBranchInitialHomFamily_evaluation :
    I ≫ leftFibrationInitialEvaluation q dB y = U :=
  pointRestrictionInitialHomFamily_evaluation (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p i) d k y

/-- 底へ射影すると、同じ元の左脚の実際の前合成を厳密に回収する。 -/
lemma specifiedCoconeLeftBranchInitialHomFamily_projection :
    I ≫ P = coconeApexHomPrecomposition dB d e y :=
  (pointRestrictionInitialHomFamily_projection (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p i) d k y).trans
      (specifiedCoconeLeftBranchPrecomposition_eq hp p c hc dB dC y)

/-- 元の左全辺族の初期制限へ至る、評価上で全時刻定値な比較データ。 -/
def specifiedCoconeLeftBranchHomCylinderData : InitialEvaluationCylinder q dB y U hB I :=
  pointRestrictionFullHomCylinderData (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p i) d k y hB
local notation "H" => specifiedCoconeLeftBranchHomCylinderData hp p c hc dB hB dC y

/-- 元の左枝の Hom 比較を、同じ実際の左脚の前合成へ結ぶ円柱。 -/
def specifiedCoconeLeftBranchHomotopy : SSet.Homotopy
    (U ≫ coconeMappingSpaceHomComparison dB hB y) (coconeApexHomPrecomposition dB d e y) :=
  homotopyEndpointTransport
    (pointRestrictionFullHomCylinder (sliceUnderProjection p) q r
      (sliceUnderRestrict_projection p i) d k y hB) rfl
    (specifiedCoconeLeftBranchPrecomposition_eq hp p c hc dB dC y)

/-- 左枝の比較は、保持した同じ評価固定中間円柱の raw な射影である。 -/
lemma specifiedCoconeLeftBranchHomotopy_projection :
    (specifiedCoconeLeftBranchHomotopy hp p c hc dB hB dC y).h = (H).homotopy.h ≫ P := by
  rw [specifiedCoconeLeftBranchHomotopy, homotopyEndpointTransport_raw]
  exact pointRestrictionFullHomCylinder_projection (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p i) d k y hB

end
end SerrePositivity.InfinityCategories.HomotopyLimits
