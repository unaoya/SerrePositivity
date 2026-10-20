module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightHomTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointRestrictionFullHomCylinder

/-!
概要：元の右枝の全辺族から、同じ実際の右脚への評価固定 Hom 比較を構成する。
方針：枝の初期制限を評価固定で始対象の切断へ結び、底の同じ前合成へ射影する。
規約：選んだ右比較辺と全 Hom の族を保持。使われ方：共通根辺との比較の整合性。
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
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC)
  (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (j ≫ p)
local notation "r" => sliceUnderRestrict p j
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "k" => SpecifiedCoconeBranchData.right (specifiedCoconeBranchData hp p c hc dB dC)
local notation "U" => coconePointHomFamily d y ≫ cosliceRestrictionFiberMap p j y
local notation "e" => coconeRestrictionEdgeApex j dC d k
local notation "P" => leftFibrationInitialProjection q dC y ≫
  Iso.hom (leftFibrationInitialBaseIso q dC y)

/-- 元の右脚の前合成は、同じ枝の初期 Hom の底の前合成そのもの。 -/
lemma specifiedCoconeRightBranchPrecomposition_eq :
    initialRestrictionHomPrecomposition (sliceUnderProjection p) q r
        (sliceUnderRestrict_projection p j) d k y = coconeApexHomPrecomposition dC d e y :=
  coconeBranchHomPrecomposition_eq dC d e y j rfl k rfl

/-- 元の右全辺族を、枝の始対象 dC の初期 Hom 空間へ移す。 -/
def specifiedCoconeRightBranchInitialHomFamily :
    pinchedHomLeft (JoinCocone.vertex d) y ⟶ leftFibrationInitialTotal q dC y :=
  pointRestrictionInitialHomFamily (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p j) d k y
local notation "I" => specifiedCoconeRightBranchInitialHomFamily hp p c hc dB dC y

/-- 初期 Hom の包含後は、元の右全辺族の同じ初期頂点制限である。 -/
lemma specifiedCoconeRightBranchInitialHomFamily_ι :
    I ≫ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm dC) ≫ q) y =
      specifiedCoconeRightFullHomFamily hp p c hc dB dC y ≫ normalizedCoconeRestriction
        (SSet.yonedaEquiv.symm (k).edge) (stdSimplex.δ (1 : Fin 2))
        (SSet.Edge.δ_one_yonedaEquiv_symm k) :=
  pointRestrictionInitialHomFamily_ι (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p j) d k y

/-- 中間族の評価は、元の全 Hom 族の右枝への制限そのもの。 -/
lemma specifiedCoconeRightBranchInitialHomFamily_evaluation :
    I ≫ leftFibrationInitialEvaluation q dC y = U :=
  pointRestrictionInitialHomFamily_evaluation (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p j) d k y

/-- 底へ射影すると、同じ元の右脚の実際の前合成を厳密に回収する。 -/
lemma specifiedCoconeRightBranchInitialHomFamily_projection :
    I ≫ P = coconeApexHomPrecomposition dC d e y :=
  (pointRestrictionInitialHomFamily_projection (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p j) d k y).trans
      (specifiedCoconeRightBranchPrecomposition_eq hp p c hc dB dC y)

/-- 元の右全辺族の初期制限へ至る、評価上で全時刻定値な比較データ。 -/
def specifiedCoconeRightBranchHomCylinderData : InitialEvaluationCylinder q dC y U hC I :=
  pointRestrictionFullHomCylinderData (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p j) d k y hC
local notation "H" => specifiedCoconeRightBranchHomCylinderData hp p c hc dB dC hC y

/-- 元の右枝の Hom 比較を、同じ実際の右脚の前合成へ結ぶ円柱。 -/
def specifiedCoconeRightBranchHomotopy : SSet.Homotopy
    (U ≫ coconeMappingSpaceHomComparison dC hC y) (coconeApexHomPrecomposition dC d e y) :=
  homotopyEndpointTransport
    (pointRestrictionFullHomCylinder (sliceUnderProjection p) q r
      (sliceUnderRestrict_projection p j) d k y hC) rfl
    (specifiedCoconeRightBranchPrecomposition_eq hp p c hc dB dC y)

/-- 右枝の比較は、保持した同じ評価固定中間円柱の raw な射影である。 -/
lemma specifiedCoconeRightBranchHomotopy_projection :
    (specifiedCoconeRightBranchHomotopy hp p c hc dB dC hC y).h = (H).homotopy.h ≫ P := by
  rw [specifiedCoconeRightBranchHomotopy, homotopyEndpointTransport_raw]
  exact pointRestrictionFullHomCylinder_projection (sliceUnderProjection p) q r
    (sliceUnderRestrict_projection p j) d k y hC

end
end SerrePositivity.InfinityCategories.HomotopyLimits
