module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeAttachmentRetractions
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftUniversalHomotopy
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightUniversalHomotopy
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeBranchToInitialHomotopies
public import SerrePositivity.InfinityCategories.HomotopyLimits.EvaluationFixedHomotopySquare

/-!
概要：普遍前置と枝比較を経る経路を、元の根辺初期族と付加辺面を経る経路へ照合する。
方針：同じ共通評価を全時刻固定する四円柱に、評価の h Fun 上の忠実性を適用する。
規約：両経路の実際の円柱と raw な射影を保持。使われ方：共通 path end の経路の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
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
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "ev" => leftFibrationInitialEvaluation q c y
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

section
local notation "H₀" => specifiedCoconeLeftUniversalInitialHomotopy hp p c hc dB hB dC y
local notation "H₁" => specifiedCoconeLeftBranchToInitialHomotopy hp p c hc dB hB dC y
local notation "H₂" => InitialEvaluationCylinder.homotopy
  (specifiedCoconeLeftHomCylinderData hp p c hc dB dC y)
local notation "H₃" => specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y

/-- 左の普遍前置・枝比較の経路は、同じ根辺初期族・付加辺面の経路と同じ類を持つ。 -/
lemma specifiedCoconeLeftAttachment_initial_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₀) ≫
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₁) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₂) ≫
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₃) := by
  have := leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  exact evaluationFixedHomotopySquare_homMk_comp ev H₀ H₁ H₂ H₃ V
    (specifiedCoconeLeftUniversalInitialHomotopy_evaluation hp p c hc dB hB dC y)
    (specifiedCoconeLeftBranchToInitialHomotopy_evaluation hp p c hc dB hB dC y)
    (specifiedCoconeLeftHomCylinderData hp p c hc dB dC y).evaluation
    (specifiedCoconeLeftAttachmentInitialHomotopy_evaluation hp p c hc dB dC y)

/-- 同じ左の四円柱を Hom へ射影しても、両経路は同じ合成の類を持つ。 -/
lemma specifiedCoconeLeftAttachment_projection_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H₀ P)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H₁ P)) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H₂ P)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H₃ P)) := by
  let G := (hoFunctor.map ((ihom T).map P)).toFunctor
  have h := congrArg G.map (specifiedCoconeLeftAttachment_initial_homMk_comp hp p c hc dB hB dC y)
  rw [G.map_comp, G.map_comp, ← functorHomotopyPostcomp_hom H₀ P,
    ← functorHomotopyPostcomp_hom H₁ P, ← functorHomotopyPostcomp_hom H₂ P,
    ← functorHomotopyPostcomp_hom H₃ P] at h
  exact h
end

section
local notation "H₀" => specifiedCoconeRightUniversalInitialHomotopy hp p c hc dB dC hC y
local notation "H₁" => specifiedCoconeRightBranchToInitialHomotopy hp p c hc dB dC hC y
local notation "H₂" => InitialEvaluationCylinder.homotopy
  (specifiedCoconeRootedHomCylinder hp p c hc dB dC y)
local notation "H₃" => specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y

/-- 右の普遍前置・枝比較の経路は、同じ根辺初期族・付加辺面の経路と同じ類を持つ。 -/
lemma specifiedCoconeRightAttachment_initial_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₀) ≫
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₁) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₂) ≫
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₃) := by
  have := leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  exact evaluationFixedHomotopySquare_homMk_comp ev H₀ H₁ H₂ H₃ V
    (specifiedCoconeRightUniversalInitialHomotopy_evaluation hp p c hc dB dC hC y)
    (specifiedCoconeRightBranchToInitialHomotopy_evaluation hp p c hc dB dC hC y)
    (specifiedCoconeRootedHomCylinder hp p c hc dB dC y).evaluation
    (specifiedCoconeRightAttachmentInitialHomotopy_evaluation hp p c hc dB dC y)

/-- 同じ右の四円柱を Hom へ射影しても、両経路は同じ合成の類を持つ。 -/
lemma specifiedCoconeRightAttachment_projection_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H₀ P)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H₁ P)) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H₂ P)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H₃ P)) := by
  let G := (hoFunctor.map ((ihom T).map P)).toFunctor
  have h := congrArg G.map (specifiedCoconeRightAttachment_initial_homMk_comp hp p c hc dB dC hC y)
  rw [G.map_comp, G.map_comp, ← functorHomotopyPostcomp_hom H₀ P,
    ← functorHomotopyPostcomp_hom H₁ P, ← functorHomotopyPostcomp_hom H₂ P,
    ← functorHomotopyPostcomp_hom H₃ P] at h
  exact h
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
