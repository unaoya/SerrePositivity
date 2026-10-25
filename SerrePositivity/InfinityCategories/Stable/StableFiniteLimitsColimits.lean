module
public import SerrePositivity.InfinityCategories.Stable.StablePushoutExistence
public import SerrePositivity.InfinityCategories.Stable.StableOpposite
public import SerrePositivity.InfinityCategories.F1.Joins.FiniteLimitGeneration
/-!
概要：IsStable の定義だけから、任意の pushout・pullback と全有限極限・余極限を導く。
方針：fiber/cofiber の貼り合わせによる span の存在を双対化し、有限形状の生成判定へ渡す。
規約：quasicategory 性と IsStable 以外の存在仮定を追加せず、全図式を元の宇宙に保持する。
使われ方：D-7′。Ind_κ(C) の有限極限・余極限と安定性への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

lemma IsStable.hasLimit_cospan {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 2 : SSet.{u}) ⟶ X) : HasLimit p := by
  apply (F1B.kanHasLimit_iff_hasColimit_op p).mpr
  apply (F1B.kanHasColimit_iff_restrict_of_isIso (SSet.opFunctor.map p)
    (hornReverseIso 2 2).hom).mpr
  exact IsStable.hasColimit_span _

lemma IsStable.exists_pushoutSquare {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    ∃ R : Δ[1] ⊗ Δ[1] ⟶ X, pushoutSpan R = p ∧ IsPushoutSquare R := by
  obtain ⟨c, hc⟩ := IsStable.hasColimit_span p
  exact ⟨coconeSquare c, coconeSquare_span c, coconeSquare_isPushout c hc⟩

lemma IsStable.exists_pullbackSquare {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    ∃ R : Δ[1] ⊗ Δ[1] ⟶ X, pullbackCospan R = p ∧ IsPullbackSquare R := by
  obtain ⟨c, hc⟩ := IsStable.hasLimit_cospan p
  exact ⟨coneSquare c, coneSquare_cospan c, coneSquare_isPullback c hc⟩

theorem hasFiniteColimits_of_isStable (X : SSet.{u}) [Quasicategory X] [IsStable X] :
    HasFiniteColimits X :=
  hasFiniteColimits_of_initial_pushouts (chosenZeroVertex X).vertex
    (chosenZeroVertex X).isInitial IsStable.hasColimit_span

theorem hasFiniteLimits_of_isStable (X : SSet.{u}) [Quasicategory X] [IsStable X] :
    HasFiniteLimits X :=
  hasFiniteLimits_of_terminal_pullbacks (chosenZeroVertex X).vertex
    (chosenZeroVertex X).isTerminal IsStable.hasLimit_cospan

theorem hasFiniteLimitsColimits_of_isStable (X : SSet.{u}) [Quasicategory X] [IsStable X] :
    HasFiniteLimits X ∧ HasFiniteColimits X :=
  ⟨hasFiniteLimits_of_isStable X, hasFiniteColimits_of_isStable X⟩

end SerrePositivity.InfinityCategories
