module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedProjectionExistence

/-!
概要：各段の twisted-arrow 引き戻しの weighted 全空間は、元の全空間の同じ引き戻し。
方針：元の二つの射影を保つ各次数の存在と一意性から、引き戻しの普遍性を証明する。
規約：充填性や filtered 性は不要。使われ方：共同 Hom の元の評価空間への厳密な移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の全空間の両射影の四角形は、同じ底上の引き戻し。 -/
lemma weightedTwistedProjections_isPullback :
    IsPullback (weightedTwistedBaseProjection F) (weightedTwistedTotalProjection F)
      (edgewiseRight C) (weightedNerveParameter (rightFibrationProjectionCocone F).ι) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨n⟩⟩
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌)) (weightedTwistedProjections_commute F)
  · intro x y h
    apply weightedTwistedProjections_jointlyInjective F n
    exact Prod.ext h.1 h.2
  · intro t s h
    exact weightedTwistedProjections_exists F t s h

/-- 元の twisted-arrow 引き戻しへの、元の両射影を持つ同じ全空間の同型。 -/
def weightedTwistedPullbackIso : weightedNerve (strictRightTwistedElementsDiagram F) ≅
    pullback (edgewiseRight C) (weightedNerveParameter (rightFibrationProjectionCocone F).ι) :=
  (weightedTwistedProjections_isPullback F).isoPullback

/-- 同じ同型の第一射影は、元の全 twisted arrow の底射影。 -/
lemma weightedTwistedPullbackIso_fst :
    (weightedTwistedPullbackIso F).hom ≫ pullback.fst _ _ = weightedTwistedBaseProjection F :=
  (weightedTwistedProjections_isPullback F).isoPullback_hom_fst

/-- 同じ同型の第二射影は、元の weighted 全空間への元の射影。 -/
lemma weightedTwistedPullbackIso_snd :
    (weightedTwistedPullbackIso F).hom ≫ pullback.snd _ _ = weightedTwistedTotalProjection F :=
  (weightedTwistedProjections_isPullback F).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.F2.Ind
