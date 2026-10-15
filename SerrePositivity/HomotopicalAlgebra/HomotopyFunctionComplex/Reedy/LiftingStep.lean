module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerTransformationNaturality
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-! # Extending a Reedy lift at one degree

A lift already natural on lower objects determines an actual square between
the relative latching map and the relative matching map. Lifting that square
supplies the new component and both boundary compatibility conditions.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.LiftingStep
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]
  {A B X Y : J ⥤ C} {i : A ⟶ B} {p : X ⟶ Y} {a : A ⟶ X} {b : B ⟶ Y}
  (sq : CommSq a i p b)
  (ℓ : lowerInclusion r (r.deg j) ⋙ B ⟶ lowerInclusion r (r.deg j) ⋙ X)
  (hi : Functor.whiskerLeft (lowerInclusion r (r.deg j)) i ≫ ℓ =
    Functor.whiskerLeft (lowerInclusion r (r.deg j)) a)
  (hp : ℓ ≫ Functor.whiskerLeft (lowerInclusion r (r.deg j)) p =
    Functor.whiskerLeft (lowerInclusion r (r.deg j)) b)

abbrev top : pushout ((latchingEvaluation r j).map i) ((latchingComparison r j).app A) ⟶ X.obj j :=
  pushout.desc (latchingExtension r j ℓ) (a.app j) (by
    rw [latchingExtension_precomp, hi, latchingExtension_restrict])

abbrev bottom : B.obj j ⟶
    pullback ((matchingComparison r j).app Y) ((matchingEvaluation r j).map p) :=
  pullback.lift (b.app j) (matchingExtension r j ℓ) (by
    rw [← matchingExtension_restrict, ← hp, ← matchingExtension_postcomp])

omit [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] in
@[reassoc (attr := simp)]
lemma inl_top : pushout.inl ((latchingEvaluation r j).map i) ((latchingComparison r j).app A) ≫
    top r j ℓ hi = latchingExtension r j ℓ := by simp [top]

omit [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] in
@[reassoc (attr := simp)]
lemma inr_top : pushout.inr ((latchingEvaluation r j).map i) ((latchingComparison r j).app A) ≫
    top r j ℓ hi = a.app j := by simp [top]

omit [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] in
@[reassoc (attr := simp)]
lemma bottom_fst : bottom r j ℓ hp ≫
    pullback.fst ((matchingComparison r j).app Y) ((matchingEvaluation r j).map p) = b.app j := by
  simp [bottom]

omit [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] in
@[reassoc (attr := simp)]
lemma bottom_snd : bottom r j ℓ hp ≫
    pullback.snd ((matchingComparison r j).app Y) ((matchingEvaluation r j).map p) =
      matchingExtension r j ℓ := by simp [bottom]

lemma square (sq : CommSq a i p b) : CommSq (top r j ℓ hi) (relativeLatchingMap r j i)
    (relativeMatchingMap r j p) (bottom r j ℓ hp) where
  w := by
    apply pullback.hom_ext
    · rw [Category.assoc, relativeMatchingMap_fst, Category.assoc, bottom_fst]
      apply pushout.hom_ext
      · have ht := inl_top r j ℓ hi
        have hi' := inl_relativeLatchingMap r j i
        rw [← Category.assoc, ht, ← Category.assoc, hi', latchingExtension_postcomp,
          hp, latchingExtension_restrict]
      · have ht := inr_top r j ℓ hi
        have hi' := inr_relativeLatchingMap r j i
        rw [← Category.assoc, ht, ← Category.assoc, hi']
        exact congr_app sq.w j
    · rw [Category.assoc, relativeMatchingMap_snd, Category.assoc, bottom_snd]
      apply pushout.hom_ext
      · have ht := inl_top r j ℓ hi
        have hi' := inl_relativeLatchingMap r j i
        rw [← Category.assoc, ht, ← Category.assoc, hi']
        exact latching_matching_extension r j ℓ
      · have ht := inr_top r j ℓ hi
        have hi' := inr_relativeLatchingMap r j i
        rw [← Category.assoc, ht, ← Category.assoc, hi', ← matchingExtension_restrict,
          ← hi, ← matchingExtension_precomp]

variable [HasLiftingProperty (relativeLatchingMap r j i) (relativeMatchingMap r j p)]

abbrev component : B.obj j ⟶ X.obj j := (square r j ℓ hi hp sq).lift

lemma component_fac_left : i.app j ≫ component r j sq ℓ hi hp = a.app j := by
  rw [← inr_relativeLatchingMap r j i, Category.assoc, (square r j ℓ hi hp sq).fac_left, inr_top]

lemma component_fac_right : component r j sq ℓ hi hp ≫ p.app j = b.app j := by
  rw [← relativeMatchingMap_fst r j p, ← Category.assoc,
    (square r j ℓ hi hp sq).fac_right, bottom_fst]

lemma latching_component : (latchingComparison r j).app B ≫ component r j sq ℓ hi hp =
    latchingExtension r j ℓ := by
  rw [← inl_relativeLatchingMap r j i, Category.assoc, (square r j ℓ hi hp sq).fac_left, inl_top]

lemma component_matching : component r j sq ℓ hi hp ≫ (matchingComparison r j).app X =
    matchingExtension r j ℓ := by
  rw [← relativeMatchingMap_snd r j p, ← Category.assoc,
    (square r j ℓ hi hp sq).fac_right, bottom_snd]

lemma incoming (f : LatchingIndex r j) :
    B.map f.obj.hom ≫ component r j sq ℓ hi hp =
      ℓ.app ((latchingSourceLower r j).obj f) ≫ X.map f.obj.hom := by
  have h := congrArg (fun m ↦ colimit.ι (latchingSource r j ⋙ B) f ≫ m)
    (latching_component r j sq ℓ hi hp)
  change colimit.ι (latchingSource r j ⋙ B) f ≫
      (colimit.desc _ (latchingCocone r B j) ≫ component r j sq ℓ hi hp) =
    colimit.ι (latchingSource r j ⋙ B) f ≫ latchingExtension r j ℓ at h
  rw [colimit.ι_desc_assoc, ι_latchingExtension] at h
  exact h

lemma outgoing (g : MatchingIndex r j) :
    component r j sq ℓ hi hp ≫ X.map g.obj.hom =
      B.map g.obj.hom ≫ ℓ.app ((matchingTargetLower r j).obj g) := by
  have h := congrArg (fun m ↦ m ≫ limit.π (matchingTarget r j ⋙ X) g)
    (component_matching r j sq ℓ hi hp)
  change (component r j sq ℓ hi hp ≫ limit.lift _ (matchingCone r X j)) ≫
      limit.π (matchingTarget r j ⋙ X) g =
    matchingExtension r j ℓ ≫ limit.π (matchingTarget r j ⋙ X) g at h
  rw [Category.assoc, limit.lift_π, matchingExtension_π] at h
  exact h

end SerrePositivity.Reedy.LiftingStep
