module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedPullbackIso
public import SerrePositivity.InfinityCategories.F2.Ind.TwistedElementsBaseChange

/-!
概要：同じ weighted 引き戻しの同型は、共同 Hom の元の始点・終点・添字を保つ。
方針：元の二つの引き戻し射影と weighted の同じ最後の係数を比較する。
規約：元の全図式の厳密な底。使われ方：共同密度の相対持ち上げを元の Hom の底へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の共同 Hom の始点を保ち、終点の元の添字を読む共同底の射。 -/
def weightedTwistedNativeJointBase : C.op ⊗ weightedNerve (rightFibrationTotalDiagram F) ⟶
    C.op ⊗ nerve I :=
  lift (fst _ _) (snd _ _ ≫ weightedNerveProjection (rightFibrationTotalDiagram F))

/-- 元の全 twisted arrow の始点評価は、同じ定値係数の評価と厳密に可換。 -/
lemma weightedTwistedBaseProjection_left :
    weightedTwistedBaseProjection F ≫ edgewiseLeft C =
      weightedNerveParameter (strictRightTwistedSourceProjection F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (edgewiseLeft C).app _
      (SSet.yonedaEquiv (s.2.app (Fin.last n) ≫ pullback.fst _ _)) =
    SSet.yonedaEquiv (s.2.app (Fin.last n) ≫ (pullback.fst _ _ ≫ edgewiseLeft C))
  rw [← SSet.yonedaEquiv_comp, Category.assoc]

/-- 元の引き戻しへの同型は、共同 Hom の始点と同じ終点添字をともに保つ。 -/
lemma weightedTwistedPullbackIso_jointBase :
    (weightedTwistedPullbackIso F).hom ≫
      twistedElementsProjection (C := C)
        (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι) ≫
        weightedTwistedNativeJointBase F = weightedTwistedSourceBase F := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, weightedTwistedNativeJointBase, lift_fst,
      twistedElementsProjection, weightedTwistedSourceBase, weightedNerveParameterProjection]
    rw [← Category.assoc, weightedTwistedPullbackIso_fst F]
    exact weightedTwistedBaseProjection_left F
  · simp only [Category.assoc, weightedTwistedNativeJointBase, lift_snd, lift_snd_assoc,
      twistedElementsProjection, weightedTwistedSourceBase, weightedNerveParameterProjection]
    rw [← Category.assoc, weightedTwistedPullbackIso_snd F]
    exact weightedNerveMap_projection (strictRightTwistedTotalProjection F)

end SerrePositivity.InfinityCategories.F2.Ind
