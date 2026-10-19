module

public import SerrePositivity.InfinityCategories.F1.TransportSimplexMarkedCover
public import SerrePositivity.InfinityCategories.F1.FullSubcomplexPullbackRestriction

/-!
概要：反転関手の貼り合わせを実際の単体集合の pullback として表す。
方針：単体圏の nerve の pushout を内部 Hom で pullback に写し、全頂点の反転条件を回収する。
規約：全高次パラメーターを同時に貼り合わせ、quasicategory 性は不要。
使われ方：一般の底の局所化を相対的に貼り合わせるための制限図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 単体圏の nerve が pushout なら、反転関手の制限図式は実際の pullback。 -/
lemma transportSimplexInverting_isPullback_of_nerve_isPushout {A B C D : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout (nerveMap (transportSimplexFunctor i))
      (nerveMap (transportSimplexFunctor g)) (nerveMap (transportSimplexFunctor k))
      (nerveMap (transportSimplexFunctor j))) (E : SSet.{u}) :
    IsPullback (transportSimplexInvertingRestriction j E)
      (transportSimplexInvertingRestriction k E)
      (transportSimplexInvertingRestriction g E)
      (transportSimplexInvertingRestriction i E) := by
  refine isPullback_fullSubcomplex_restriction (isPullback_pre_of_isPushout h E)
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges D))
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges C))
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges B))
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges A))
    (transportSimplexInvertingRestriction j E) (transportSimplexInvertingRestriction k E)
    (transportSimplexInvertingRestriction g E) (transportSimplexInvertingRestriction i E)
    (transportSimplexInvertingRestriction_ι j E) (transportSimplexInvertingRestriction_ι k E)
    (transportSimplexInvertingRestriction_ι g E) (transportSimplexInvertingRestriction_ι i E) ?_
  intro a hC hB
  obtain ⟨U, rfl⟩ := (functorVertexEquiv (nerve (TransportSimplexCategory D)) E).surjective a
  change InvertsEdges ((functorVertexEquiv _ E).symm ((functorVertexEquiv _ E) U)) _
  rw [Equiv.symm_apply_apply]
  change InvertsEdges ((functorVertexEquiv _ E).symm ((functorVertexEquiv _ E)
    (nerveMap (transportSimplexFunctor j) ≫ U))) _ at hC
  change InvertsEdges ((functorVertexEquiv _ E).symm ((functorVertexEquiv _ E)
    (nerveMap (transportSimplexFunctor k) ≫ U))) _ at hB
  rw [Equiv.symm_apply_apply] at hC hB
  exact (transportSimplexInvertsEdges_of_isPushout h U).mpr ⟨hB, hC⟩

/-- 部分複体の共通部分と合併による分解では、反転関手は全次数で貼り合わさる。 -/
lemma transportSimplexInverting_bicart_isPullback {B : SSet.{u}}
    {K₁ K₂ K₃ K₄ : B.Subcomplex} (h : Subcomplex.BicartSq K₁ K₂ K₃ K₄)
    (E : SSet.{u}) :
    IsPullback
      (transportSimplexInvertingRestriction (Subcomplex.homOfLE h.le₃₄) E)
      (transportSimplexInvertingRestriction (Subcomplex.homOfLE h.le₂₄) E)
      (transportSimplexInvertingRestriction (Subcomplex.homOfLE h.le₁₃) E)
      (transportSimplexInvertingRestriction (Subcomplex.homOfLE h.le₁₂) E) :=
  transportSimplexInverting_isPullback_of_nerve_isPushout
    (transportSimplexNerve_bicart_isPushout h) E

end SerrePositivity.InfinityCategories
