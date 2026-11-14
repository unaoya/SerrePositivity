module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.StrictPathPullbackMap

/-! 入力制限後の同一対角の引き戻しから、元の対角引き戻しへ戻す一般射。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits SSet
variable {E F I J Q A B : SSet.{u}} (p : E ⟶ I) (q : F ⟶ J)
  (d : E ⟶ Q) (e : F ⟶ Q) (a : A ⟶ I) (b : B ⟶ J)

def dgGluingRestrictedDiagonalStrictForget :
    pullback (pullback.fst p a ≫ d) (pullback.fst q b ≫ e) ⟶ pullback e d :=
  pullback.lift
    (pullback.snd (pullback.fst p a ≫ d) (pullback.fst q b ≫ e) ≫ pullback.fst q b)
    (pullback.fst (pullback.fst p a ≫ d) (pullback.fst q b ≫ e) ≫ pullback.fst p a) (by
      simpa only [Category.assoc] using
        (pullback.condition (f := pullback.fst p a ≫ d) (g := pullback.fst q b ≫ e)).symm)

lemma dgGluingRestrictedDiagonalStrictForget_first :
    dgGluingRestrictedDiagonalStrictForget p q d e a b ≫ pullback.fst e d =
      pullback.snd (pullback.fst p a ≫ d) (pullback.fst q b ≫ e) ≫ pullback.fst q b :=
  pullback.lift_fst _ _ _

lemma dgGluingRestrictedDiagonalStrictForget_last :
    dgGluingRestrictedDiagonalStrictForget p q d e a b ≫ pullback.snd e d =
      pullback.fst (pullback.fst p a ≫ d) (pullback.fst q b ≫ e) ≫ pullback.fst p a :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
