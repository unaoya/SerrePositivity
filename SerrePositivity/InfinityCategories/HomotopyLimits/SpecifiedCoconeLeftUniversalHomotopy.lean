module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentUniversalCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeEndHomotopies

/-!
概要：左の普遍前置への円柱を、元の指定余錐の全 Hom パラメータで表示する。
方針：同じ元の制限を前合成し、raw な射影と元の HL の同じ類を保つ。
規約：共通評価を全時刻固定。使われ方：前置後の枝円柱との同じ初期 Hom 上の接続。
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
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => pinchedHomLeft (JoinCocone.vertex d) y
local notation "U" => coconePointHomFamily d y ≫ cosliceRestrictionFiberMap p i y
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "R" => normalizedCoconeRestrictionFiber (i ≫ p) f rfl y
local notation "D₀" => colimitAttachmentUniversalCylinderData c hc f (i ≫ p) rfl dB hB y
local notation "Φ" => colimitAttachmentTotalPrecomposition c hc f (i ≫ p) rfl dB y
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)
local notation "H" => colimitAttachmentUniversalHomCylinder c hc f (i ≫ p) rfl dB hB y

/-- 同じ共通評価から、左の前置後の枝円柱の始点へ至る実際の円柱。 -/
def specifiedCoconeLeftUniversalInitialHomotopy : SSet.Homotopy
    (V ≫ leftFibrationInitialSection q c hc y)
    ((U ≫ leftFibrationInitialSection (sliceUnderProjection (i ≫ p)) dB hB y) ≫ Φ) :=
  homotopyEndpointTransport (functorHomotopyPrecomp (D₀).homotopy U)
    ((Category.assoc U R (leftFibrationInitialSection q c hc y)).symm.trans
      (congrArg (· ≫ leftFibrationInitialSection q c hc y)
        (specifiedCoconeLeftHomRestriction_common hp p c hc dB dC y)))
    (Category.assoc _ _ _).symm

/-- 元の共通 Hom 族は、この円柱の全時刻で厳密に評価される。 -/
lemma specifiedCoconeLeftUniversalInitialHomotopy_evaluation :
    (specifiedCoconeLeftUniversalInitialHomotopy hp p c hc dB hB dC y).h ≫
        leftFibrationInitialEvaluation q c y = fst T Δ[1] ≫ V := by
  rw [specifiedCoconeLeftUniversalInitialHomotopy, homotopyEndpointTransport_raw]
  change ((U ▷ Δ[1]) ≫ (D₀).homotopy.h) ≫ _ = _
  calc
    _ = (U ▷ Δ[1]) ≫ ((D₀).homotopy.h ≫ leftFibrationInitialEvaluation q c y) :=
      Category.assoc _ _ _
    _ = (U ▷ Δ[1]) ≫ (fst _ Δ[1] ≫ R) := congrArg ((U ▷ Δ[1]) ≫ ·) (D₀).evaluation
    _ = ((U ▷ Δ[1]) ≫ fst _ Δ[1]) ≫ R := (Category.assoc _ _ _).symm
    _ = (fst T Δ[1] ≫ U) ≫ R := congrArg (· ≫ R) (whiskerRight_fst U Δ[1])
    _ = fst T Δ[1] ≫ V := (Category.assoc _ _ _).trans
      (congrArg (fst T Δ[1] ≫ ·) (specifiedCoconeLeftHomRestriction_common hp p c hc dB dC y))

/-- 同じ評価固定円柱を通常 Hom へ射影した、共通始点を持つ円柱。 -/
def specifiedCoconeLeftUniversalHomotopy : SSet.Homotopy
    (V ≫ coconeMappingSpaceHomComparison c hc y)
    (U ≫ coconeMappingSpaceHomComparison dB hB y ≫
      colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y) :=
  homotopyEndpointTransport (functorHomotopyPrecomp H U)
    ((Category.assoc U R (coconeMappingSpaceHomComparison c hc y)).symm.trans
      (congrArg (· ≫ coconeMappingSpaceHomComparison c hc y)
        (specifiedCoconeLeftHomRestriction_common hp p c hc dB dC y))) rfl

/-- 底の円柱は同じ初期 Hom 円柱の raw な射影である。 -/
lemma specifiedCoconeLeftUniversalHomotopy_projection :
    (specifiedCoconeLeftUniversalHomotopy hp p c hc dB hB dC y).h =
      (specifiedCoconeLeftUniversalInitialHomotopy hp p c hc dB hB dC y).h ≫ P := by
  rw [specifiedCoconeLeftUniversalHomotopy, homotopyEndpointTransport_raw,
    specifiedCoconeLeftUniversalInitialHomotopy, homotopyEndpointTransport_raw]
  change (U ▷ Δ[1]) ≫ (H).h = ((U ▷ Δ[1]) ≫ (D₀).homotopy.h) ≫ P
  rw [colimitAttachmentUniversalHomCylinder_projection, Category.assoc]

/-- 共通 Hom パラメータへの制限後も、元の同じ HL の射の類を回収する。 -/
lemma specifiedCoconeLeftUniversalHomotopy_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftUniversalHomotopy hp p c hc dB hB dC y))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y))) := by
  have h := colimitAttachmentUniversalHomCylinder_hom_arrow c hc f (i ≫ p) rfl dB hB y
  have hpre := SerrePositivity.InfinityCategories.functorHomotopy_precomp_hom_arrow _ _ h U
  have hu := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq
    (specifiedCoconeLeftUniversalHomotopy hp p c hc dB hB dC y) (functorHomotopyPrecomp H U)
    (by rw [specifiedCoconeLeftUniversalHomotopy, homotopyEndpointTransport_raw])
  have ho := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq
    (specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y)
    (functorHomotopyPrecomp
      (colimitAttachmentRestrictionHomCylinder c hc f (i ≫ p) rfl dB hB y) U)
    (specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)
  exact hu.trans (hpre.trans ho.symm)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
