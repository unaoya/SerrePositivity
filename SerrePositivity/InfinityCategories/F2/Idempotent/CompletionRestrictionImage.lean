module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionRestriction
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition

/-!
概要：元の任意の冪等完備化への制限は、全関手空間で充満忠実。
方針：元の頂点像の全部分圏へ因子化し、元の同値と全部分圏の包含への制限を合成する。
規約：元の射の単射性や inner fibration 性は仮定しない。
使われ方：元の idemYoneda に沿う HTT 5.1.4.9 の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の冪等完備化の頂点像の全部分圏の包含も、同じ標的の冪等完備化。 -/
lemma IsIdempotentCompletion.vertexImage {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f) :
    IsIdempotentCompletion (fullSubcomplexOnVertices D
      (fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y)).ι := by
  refine ⟨hf.1, isFullyFaithful_fullSubcomplexOnVertices_ι _ _, ?_⟩
  intro d
  obtain ⟨c, hc⟩ := hf.2.2 d
  let e := fullSubcomplexLift (fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y) f
    (fun x ↦ ⟨x, rfl⟩)
  exact ⟨e.app (Opposite.op ⦋0⦌) c, hc⟩

/-- 元の任意の冪等完備化に沿う同じ制限は、全関手の全写像空間で充満忠実。 -/
lemma IsIdempotentCompletion.pre_isFullyFaithful_general {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (f : C ⟶ D) (hf : IsIdempotentCompletion f) : IsFullyFaithful ((pre f).app E) := by
  let P := fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y
  let e := fullSubcomplexLift P f (fun x ↦ ⟨x, rfl⟩)
  let i := (fullSubcomplexOnVertices D P).ι
  have hi : IsIdempotentCompletion i := IsIdempotentCompletion.vertexImage f hf
  have h := IsIdempotentCompletion.pre_isFullyFaithful (D := E) i hi
  have he : IsQCatEquivalence e := fullSubcomplexVertexImageLift_isQCatEquivalence f hf.2.1
  have hfac : e ≫ i = f := fullSubcomplexLift_ι _ _ _
  rw [← hfac, pre_map, NatTrans.comp_app]
  exact h.comp (he.precompose E).isFullyFaithful

/-- 元の全 Yoneda の冪等完備化への因子化に沿う制限は、全写像空間で充満忠実。 -/
lemma idemYoneda_pre_isFullyFaithful (C : SSet.{u}) [Quasicategory C]
    (E : SSet.{u + 1}) [Quasicategory E] : IsFullyFaithful ((pre (idemYoneda C)).app E) :=
  IsIdempotentCompletion.pre_isFullyFaithful_general (idemYoneda C)
    (idemYoneda_isIdempotentCompletion C)

end SerrePositivity.InfinityCategories.F2.Idempotent
