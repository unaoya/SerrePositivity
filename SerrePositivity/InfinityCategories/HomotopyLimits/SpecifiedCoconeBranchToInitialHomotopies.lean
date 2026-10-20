module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTotalPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftBranchHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightBranchHom

/-!
概要：元の左右の枝の Hom 比較円柱に、実際の付加比較辺を同時に前置する。
方針：初期 Hom 間の前置写像へ同じ円柱を後合成し、評価と底の raw な式を計算する。
規約：枝の元の円柱と付加辺の既存の前合成を保持。使われ方：native 根辺比較との照合。
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
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "qA" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "qB" => sliceUnderProjection (i ≫ p)
local notation "qC" => sliceUnderProjection (j ≫ p)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => pinchedHomLeft (JoinCocone.vertex d) y
local notation "UL" => coconePointHomFamily d y ≫ cosliceRestrictionFiberMap p i y
local notation "UR" => coconePointHomFamily d y ≫ cosliceRestrictionFiberMap p j y
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "RL" => normalizedCoconeRestrictionFiber (i ≫ p) f rfl y
local notation "RR" => normalizedCoconeRestrictionFiber (j ≫ p) g
  (coconePushoutBoundary_eq hp p) y
local notation "DB" => specifiedCoconeLeftBranchHomCylinderData hp p c hc dB hB dC y
local notation "DC" => specifiedCoconeRightBranchHomCylinderData hp p c hc dB dC hC y
local notation "ΦL" => colimitAttachmentTotalPrecomposition c hc f (i ≫ p) rfl dB y
local notation "ΦR" => colimitAttachmentTotalPrecomposition c hc g (j ≫ p)
  (coconePushoutBoundary_eq hp p) dC y
local notation "PA" => leftFibrationInitialProjection qA c y ≫
  Iso.hom (leftFibrationInitialBaseIso qA c y)

/-- 元の左枝の同じ評価固定円柱を、付加比較辺で共通始対象の初期 Hom へ写す。 -/
def specifiedCoconeLeftBranchToInitialHomotopy : SSet.Homotopy
    ((UL ≫ leftFibrationInitialSection qB dB hB y) ≫ ΦL)
    (specifiedCoconeLeftBranchInitialHomFamily hp p c hc dB dC y ≫ ΦL) :=
  functorHomotopyPostcomp (DB).homotopy ΦL

/-- 右も、元の同じ枝円柱と実際の右付加辺を使う。 -/
def specifiedCoconeRightBranchToInitialHomotopy : SSet.Homotopy
    ((UR ≫ leftFibrationInitialSection qC dC hC y) ≫ ΦR)
    (specifiedCoconeRightBranchInitialHomFamily hp p c hc dB dC y ≫ ΦR) :=
  functorHomotopyPostcomp (DC).homotopy ΦR

/-- 左枝の前置後も、同じ共通終点の全族を円柱の全時刻で保持する。 -/
lemma specifiedCoconeLeftBranchToInitialHomotopy_evaluation :
    (specifiedCoconeLeftBranchToInitialHomotopy hp p c hc dB hB dC y).h ≫
        leftFibrationInitialEvaluation qA c y = fst T Δ[1] ≫ V := by
  have hv : UL ≫ RL = V := by
    simpa only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id,
      Category.assoc] using (specifiedCoconeLeftCommonHomFamily_eq hp p c hc dB dC y)
  change ((DB).homotopy.h ≫ ΦL) ≫ leftFibrationInitialEvaluation qA c y = _
  calc
    _ = (DB).homotopy.h ≫ (leftFibrationInitialEvaluation qB dB y ≫ RL) :=
      (Category.assoc _ _ _).trans (congrArg ((DB).homotopy.h ≫ ·)
        (colimitAttachmentTotalPrecomposition_evaluation c hc f (i ≫ p) rfl dB y))
    _ = ((DB).homotopy.h ≫ leftFibrationInitialEvaluation qB dB y) ≫ RL :=
      (Category.assoc _ _ _).symm
    _ = (fst T Δ[1] ≫ UL) ≫ RL := congrArg (· ≫ RL) (DB).evaluation
    _ = _ := (Category.assoc _ _ _).trans (congrArg (fst T Δ[1] ≫ ·) hv)

/-- 右枝の前置後も、全く同じ共通終点の全族を全時刻で評価する。 -/
lemma specifiedCoconeRightBranchToInitialHomotopy_evaluation :
    (specifiedCoconeRightBranchToInitialHomotopy hp p c hc dB dC hC y).h ≫
        leftFibrationInitialEvaluation qA c y = fst T Δ[1] ≫ V := by
  have hv : UR ≫ RR = V := Category.assoc _ _ _
  change ((DC).homotopy.h ≫ ΦR) ≫ leftFibrationInitialEvaluation qA c y = _
  calc
    _ = (DC).homotopy.h ≫ (leftFibrationInitialEvaluation qC dC y ≫ RR) :=
      (Category.assoc _ _ _).trans (congrArg ((DC).homotopy.h ≫ ·)
        (colimitAttachmentTotalPrecomposition_evaluation c hc g (j ≫ p)
          (coconePushoutBoundary_eq hp p) dC y))
    _ = ((DC).homotopy.h ≫ leftFibrationInitialEvaluation qC dC y) ≫ RR :=
      (Category.assoc _ _ _).symm
    _ = (fst T Δ[1] ≫ UR) ≫ RR := congrArg (· ≫ RR) (DC).evaluation
    _ = _ := (Category.assoc _ _ _).trans (congrArg (fst T Δ[1] ≫ ·) hv)

/-- 左枝の底は、元の同じ枝 Hom 円柱に既存の付加辺の前合成を続けた raw な射。 -/
lemma specifiedCoconeLeftBranchToInitialHomotopy_projection :
    (specifiedCoconeLeftBranchToInitialHomotopy hp p c hc dB hB dC y).h ≫ PA =
      (specifiedCoconeLeftBranchHomotopy hp p c hc dB hB dC y).h ≫
        colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y := by
  rw [specifiedCoconeLeftBranchHomotopy_projection]
  have h := congrArg ((DB).homotopy.h ≫ ·)
    (colimitAttachmentTotalPrecomposition_pinched c hc f (i ≫ p) rfl dB y)
  simpa only [specifiedCoconeLeftBranchToInitialHomotopy, functorHomotopyPostcomp,
    Category.assoc] using h

/-- 右も、同じ元の枝 Hom 円柱の既存の付加辺による raw な像そのもの。 -/
lemma specifiedCoconeRightBranchToInitialHomotopy_projection :
    (specifiedCoconeRightBranchToInitialHomotopy hp p c hc dB dC hC y).h ≫ PA =
      (specifiedCoconeRightBranchHomotopy hp p c hc dB dC hC y).h ≫
        colimitAttachmentHomPrecomposition c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y := by
  rw [specifiedCoconeRightBranchHomotopy_projection]
  have h := congrArg ((DC).homotopy.h ≫ ·)
    (colimitAttachmentTotalPrecomposition_pinched c hc g (j ≫ p)
      (coconePushoutBoundary_eq hp p) dC y)
  simpa only [specifiedCoconeRightBranchToInitialHomotopy, functorHomotopyPostcomp,
    Category.assoc] using h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
