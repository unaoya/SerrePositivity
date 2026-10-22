module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionFibers
public import SerrePositivity.InfinityCategories.F2.Idempotent.StabilityUniverse
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessUniverse
public import SerrePositivity.InfinityCategories.Stable.BicartesianCriterion

/-!
概要：安定 ∞ 圏の任意の冪等完備化は安定であり、元の Idem(C) 自身も安定。
方針：指定辺を保つ実際の双普遍 fiber/cofiber を構成し、零角の双方向判定を導く。
規約：HA 1.1.3.7。元の全 coherent 分裂を使用し、標的の安定性を入力に置かない。
使われ方：Cat^perf の冪等完備化と compact 対象との同定の安定性条件。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 安定な元の ∞ 圏の任意の冪等完備化は、元の全普遍四角形の意味で安定。 -/
lemma IsIdempotentCompletion.isStable {C D : SSet.{u}}
    [Quasicategory C] [IsStable C] [Quasicategory D] (f : C ⟶ D)
    (hf : IsIdempotentCompletion f) : IsStable D := by
  have : HasZeroVertex D := IsIdempotentCompletion.hasZeroVertex f hf
  exact isStable_of_bicartesian_choices
    (fun a ↦ IsIdempotentCompletion.bicartesian_fiber_exists f hf a)
    (fun a ↦ IsIdempotentCompletion.bicartesian_cofiber_exists f hf a)

/-- 安定な元の C の元の Yoneda retract 閉包 Idem(C) は、実際の安定 ∞ 圏。 -/
instance idem_isStable (C : SSet.{u}) [Quasicategory C] [IsStable C] : IsStable (Idem C) := by
  have : IsStable ((SSet.uliftFunctor.{u + 1, u}).obj C) := isStable_ulift
  exact IsIdempotentCompletion.isStable (idemYoneda C) (idemYoneda_isIdempotentCompletion C)

end SerrePositivity.InfinityCategories.F2.Idempotent
