module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinLeftCriterion
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRightCriterion
public import SerrePositivity.InfinityCategories.Stable.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion

/-!
概要：Kan の各 slice の普遍錐を使って、境界上の局所図式を単体全体へ延長する。
方針：普遍錐の相対始点・終点境界充填を uncurry し、図式部分も厳密に保つ。
規約：局所問題の解の存在を証明する。異なる slice の解の自然な組み立ては別に必要。
使われ方：Kerodon Proposition 7.3.6.7 の局所持ち上げ問題 (7.37) の絶対版。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始点が普遍余錐である境界の族を、図式部分を保って単体へ延長する。
方針：curry により余錐制限の相対始点充填を使い、uncurry で積上の族へ戻す。
規約：単体の他の頂点で余極限性を仮定しない。
使われ方：左 Kan の局所境界問題の解。 -/
lemma IsColimitCone.exists_boundaryFamily_lift {J D : SSet.{u}} [Quasicategory D]
    {p : J ⟶ D} {c : JoinCocone p} (hc : IsColimitCone c) (n : ℕ)
    (b : join J (Δ[0] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ D)
    (g : J ⊗ (Δ[n + 1] : SSet.{u}) ⟶ D)
    (hb : boundaryVertex n 0 ≫ curry b = SSet.yonedaEquiv.symm (functorVertex c.val))
    (hbg : (joinInl J (Δ[0] : SSet.{u}) ▷ (boundary (n + 1) : SSet.{u})) ≫ b =
      (J ◁ (boundary (n + 1)).ι) ≫ g) :
    ∃ H : join J (Δ[0] : SSet.{u}) ⊗ (Δ[n + 1] : SSet.{u}) ⟶ D,
      (join J (Δ[0] : SSet.{u}) ◁ (boundary (n + 1)).ι) ≫ H = b ∧
      (joinInl J (Δ[0] : SSet.{u}) ▷ (Δ[n + 1] : SSet.{u})) ≫ H = g := by
  have sq : CommSq (curry b) (boundary (n + 1)).ι (coconeRestriction J D) (curry g) := by
    constructor
    apply uncurry_injective
    dsimp only [coconeRestriction, coneRestriction]
    rw [uncurry_pre_app, uncurry_natural_left, uncurry_curry, uncurry_curry]
    exact hbg
  obtain ⟨F, hF, hFg⟩ := hc.initialBoundaryLifting n (curry b) (curry g) hb sq
  refine ⟨uncurry F, ?_, ?_⟩
  · rw [← uncurry_natural_left, hF, uncurry_curry]
  · have h := congrArg uncurry hFg
    dsimp only [coconeRestriction, coneRestriction] at h
    rw [uncurry_pre_app, uncurry_curry] at h
    exact h

/-- 概要：終点が普遍錐である境界の族を、図式部分を保って単体へ延長する。
方針：錐制限の相対終点境界充填を curry と uncurry で移す。
規約：他の頂点で極限性を要求しない。
使われ方：右 Kan の局所境界問題の解。 -/
lemma IsLimitCone.exists_boundaryFamily_lift {J D : SSet.{u}} [Quasicategory D]
    {p : J ⟶ D} {c : JoinCone p} (hc : IsLimitCone c) (n : ℕ)
    (b : join (Δ[0] : SSet.{u}) J ⊗ (boundary (n + 1) : SSet.{u}) ⟶ D)
    (g : J ⊗ (Δ[n + 1] : SSet.{u}) ⟶ D)
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ curry b =
      SSet.yonedaEquiv.symm (functorVertex c.val))
    (hbg : (joinInr (Δ[0] : SSet.{u}) J ▷ (boundary (n + 1) : SSet.{u})) ≫ b =
      (J ◁ (boundary (n + 1)).ι) ≫ g) :
    ∃ H : join (Δ[0] : SSet.{u}) J ⊗ (Δ[n + 1] : SSet.{u}) ⟶ D,
      (join (Δ[0] : SSet.{u}) J ◁ (boundary (n + 1)).ι) ≫ H = b ∧
      (joinInr (Δ[0] : SSet.{u}) J ▷ (Δ[n + 1] : SSet.{u})) ≫ H = g := by
  have sq : CommSq (curry b) (boundary (n + 1)).ι (coneRestriction J D) (curry g) := by
    constructor
    apply uncurry_injective
    dsimp only [coconeRestriction, coneRestriction]
    rw [uncurry_pre_app, uncurry_natural_left, uncurry_curry, uncurry_curry]
    exact hbg
  obtain ⟨F, hF, hFg⟩ :=
    terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc n (curry b) (curry g) hb sq
  refine ⟨uncurry F, ?_, ?_⟩
  · rw [← uncurry_natural_left, hF, uncurry_curry]
  · have h := congrArg uncurry hFg
    dsimp only [coconeRestriction, coneRestriction] at h
    rw [uncurry_pre_app, uncurry_curry] at h
    exact h

/-- 概要：左 Kan の厳密化の各 slice 上で局所境界問題は解を持つ。
方針：元の指定変換の左 Kan 条件を局所余極限性へ移し、境界の族を延長する。
規約：δ の単射性・C の quasicategory 性は不要。解の大域的な組み立ては含めない。
使われ方：全部分 ∞ 圏からの制限定理の局所入力。 -/
lemma LeftKanRelativeJoinRealization.Strictification.exists_localBoundary_lift
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification)
    (hβ : IsLeftKanExtension δ F₀ F β) (c : C _⦋0⦌) (n : ℕ)
    (b : join (leftKanShape δ c) (Δ[0] : SSet.{u}) ⊗
      (boundary (n + 1) : SSet.{u}) ⟶ D)
    (g : leftKanShape δ c ⊗ (Δ[n + 1] : SSet.{u}) ⟶ D)
    (hb : boundaryVertex n 0 ≫ curry b = SSet.yonedaEquiv.symm
      (functorVertex (kanRelativeJoinDiagramCocone δ c r.diagram).val))
    (hbg : (joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}) ▷
        (boundary (n + 1) : SSet.{u})) ≫ b =
      (leftKanShape δ c ◁ (boundary (n + 1)).ι) ≫ g) :
    ∃ H : join (leftKanShape δ c) (Δ[0] : SSet.{u}) ⊗ (Δ[n + 1] : SSet.{u}) ⟶ D,
      (join (leftKanShape δ c) (Δ[0] : SSet.{u}) ◁ (boundary (n + 1)).ι) ≫ H = b ∧
      (joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}) ▷ (Δ[n + 1] : SSet.{u})) ≫ H = g :=
  (r.isLeftKanExtension_iff_local_colimits.1 hβ c).exists_boundaryFamily_lift n b g hb hbg

/-- 概要：右 Kan の厳密化の各 coslice 上で局所境界問題は解を持つ。
方針：元の右 Kan 条件を局所極限性へ移し、終点を固定した境界の族を延長する。
規約：局所解の存在だけを結論する。
使われ方：右 Kan の写像空間の制限定理の局所入力。 -/
lemma RightKanRelativeJoinRealization.Strictification.exists_localBoundary_lift
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification)
    (hα : IsRightKanExtension δ F₀ F α) (c : C _⦋0⦌) (n : ℕ)
    (b : join (Δ[0] : SSet.{u}) (rightKanShape δ c) ⊗
      (boundary (n + 1) : SSet.{u}) ⟶ D)
    (g : rightKanShape δ c ⊗ (Δ[n + 1] : SSet.{u}) ⟶ D)
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ curry b = SSet.yonedaEquiv.symm
      (functorVertex (kanRelativeJoinDiagramCone δ c r.diagram).val))
    (hbg : (joinInr (Δ[0] : SSet.{u}) (rightKanShape δ c) ▷
        (boundary (n + 1) : SSet.{u})) ≫ b =
      (rightKanShape δ c ◁ (boundary (n + 1)).ι) ≫ g) :
    ∃ H : join (Δ[0] : SSet.{u}) (rightKanShape δ c) ⊗ (Δ[n + 1] : SSet.{u}) ⟶ D,
      (join (Δ[0] : SSet.{u}) (rightKanShape δ c) ◁ (boundary (n + 1)).ι) ≫ H = b ∧
      (joinInr (Δ[0] : SSet.{u}) (rightKanShape δ c) ▷ (Δ[n + 1] : SSet.{u})) ≫ H = g :=
  (r.isRightKanExtension_iff_local_limits.1 hα c).exists_boundaryFamily_lift n b g hb hbg

end SerrePositivity.InfinityCategories
