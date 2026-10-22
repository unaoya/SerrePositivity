module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionPointed
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessUniverse

/-!
概要：元の Idem(C) は、元の C の零対象をそのまま Yoneda 像の零対象として持つ。
方針：元の零頂点を宇宙持ち上げし、元の冪等完備化の零対象保存を適用する。
規約：同じ元の頂点の像を保持する。安定性の残りの条件は別工程。
使われ方：HA 1.1.3.7 の冪等完備化の安定性の零対象条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の C の指定零頂点の同じ Yoneda 像は、元の Idem(C) の零頂点。 -/
lemma idemYoneda_isZeroVertex {C : SSet.{u}} [Quasicategory C]
    {z : C _⦋0⦌} (hz : IsZeroVertex z) :
    IsZeroVertex ((idemYoneda C).app (Opposite.op ⦋0⦌) (ULift.up z)) := by
  have h₀ : IsZeroVertex (X := (SSet.uliftFunctor.{u + 1, u}).obj C) (ULift.up z) :=
    ⟨(isInitialVertex_iff_ulift z).mp hz.1, (isTerminalVertex_iff_ulift z).mp hz.2⟩
  exact IsIdempotentCompletion.map_isZeroVertex (idemYoneda C)
    (idemYoneda_isIdempotentCompletion C) h₀

/-- 元の C が pointed なら、元の Yoneda retract 閉包 Idem(C) も pointed。 -/
instance idem_hasZeroVertex (C : SSet.{u}) [Quasicategory C] [HasZeroVertex C] :
    HasZeroVertex (Idem C) := by
  obtain ⟨z, hz⟩ := HasZeroVertex.exists_zero (X := C)
  exact ⟨(idemYoneda C).app (Opposite.op ⦋0⦌) (ULift.up z), idemYoneda_isZeroVertex hz⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
