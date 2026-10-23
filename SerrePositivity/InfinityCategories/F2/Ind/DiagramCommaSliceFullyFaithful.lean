module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramComma
public import SerrePositivity.InfinityCategories.F2.Ind.FullyFaithfulPullbackRight
public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundarySliceReflection

/-!
概要：実 diagram comma の slice 射影の充満忠実性と、全族の同型の反映。
方針：元の図式 Yoneda の充満忠実性を、実 slice の right fibration に沿って移す。
規約：Yoneda に充填性を仮定しない。使われ方：再構成全余錐から元の q の族へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)

/-- 元の図式 comma から、指定元図式 D の実 slice への第二射影。 -/
abbrev diagramCommaSliceProjection : diagramComma κ D ⟶
    sliceOver (SSet.yonedaEquiv.symm (functorVertex D)) :=
  pullback.snd (diagramYoneda κ K C)
    (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex D)))

/-- 元の全図式 Yoneda が充満忠実なので、実 comma の同じ第二射影も充満忠実。 -/
lemma diagramCommaSliceProjection_isFullyFaithful :
    IsFullyFaithful (diagramCommaSliceProjection κ D) :=
  fullyFaithful_pullback_snd_of_innerFibration_right
    (diagramYoneda_isFullyFaithful κ K C)
    (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex D)))

/-- 任意の全パラメーター族の slice 像の同型を、同じ元の comma の族へ戻す。 -/
def diagramCommaFunctorIsoOfSliceIso {T : SSet.{u + 1}} (f g : T ⟶ diagramComma κ D)
    (e : FunctorIso (f ≫ diagramCommaSliceProjection κ D)
      (g ≫ diagramCommaSliceProjection κ D)) : FunctorIso f g :=
  (diagramCommaSliceProjection_isFullyFaithful κ D).preimageFunctorIso e

end SerrePositivity.InfinityCategories.F2.Ind
