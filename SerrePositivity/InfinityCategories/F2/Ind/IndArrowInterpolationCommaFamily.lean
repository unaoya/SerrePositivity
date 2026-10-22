module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationLiftedCocone

/-!
概要：補間した小さい全 C 図式と指定 D への全余錐を、元の図式 comma へ戻す。
方針：指定頂点を厳密に回収した余錐と、実 comma の族の普遍性を使う。
規約：元の q への境界制限の一致は未主張。使われ方：射図式の filtered 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)

/-- 同じ小さい補間図式と、同じ指定 D への全変換が定める元の図式 comma の族。 -/
def indArrowInterpolationCommaFamily :
    (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶ diagramComma κ D :=
  commaFamilyLift (diagramYoneda κ Δ[1] C) (functorVertex D)
    ((SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V))
    (indArrowInterpolationLiftedCoconeMap V)
    (indArrowInterpolationLiftedCoconeMap_old V) (indArrowInterpolationLiftedCoconeMap_tip V)

/-- 元の C の小さい全図式への射影は厳密に回収される。 -/
lemma indArrowInterpolationCommaFamily_projection :
    indArrowInterpolationCommaFamily V ≫ diagramCommaProjection κ D =
      (SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V) :=
  commaFamilyLift_projection _ _ _ _ _ _

/-- 同じ元の図式 comma から読む全余錐は、構成した全余錐そのもの。 -/
lemma indArrowInterpolationCommaFamily_uncurry :
    sliceOverUncurry (indArrowInterpolationCommaFamily V ≫
      pullback.snd (diagramYoneda κ (Δ[1] : SSet.{u}) C)
        (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex D)))) =
      indArrowInterpolationLiftedCoconeMap V :=
  commaFamilyLift_uncurry _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
