module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LiftBelow

/-! # A successor step for a lift natural below a Reedy degree

Old components are retained. New components come from the actual relative
lifting squares; naturality inside the new degree uses unique Reedy
factorization and the absence of nonidentity same-degree direct/inverse maps.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.LiftBelow
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {r : ReedyStructure inverse direct ℕ} {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {A B X Y : J ⥤ C} {i : A ⟶ B} {p : X ⟶ Y} {a : A ⟶ X} {b : B ⟶ Y}
  {sq : CommSq a i p b}
  [∀ j, HasLiftingProperty (relativeLatchingMap r j i) (relativeMatchingMap r j p)]
  {n : ℕ} (l : LiftBelow r sq n)

abbrev newComponent (j : J) (hj : r.deg j ≤ n) : B.obj j ⟶ X.obj j :=
  LiftingStep.component r j sq (l.restrictAt j hj)
    (l.restrictAt_fac_left j hj) (l.restrictAt_fac_right j hj)

abbrev stepApp (j : Lower r (n + 1)) : B.obj j.obj ⟶ X.obj j.obj :=
  if hj : r.deg j.obj < n then l.hom.app ⟨j.obj, hj⟩
  else l.newComponent j.obj (Nat.le_of_lt_succ j.property)

lemma stepApp_fac_left (j : Lower r (n + 1)) : i.app j.obj ≫ l.stepApp j = a.app j.obj := by
  unfold stepApp
  split_ifs with hj
  · exact congr_app l.fac_left ⟨j.obj, hj⟩
  · exact LiftingStep.component_fac_left r j.obj sq _ _ _

lemma stepApp_fac_right (j : Lower r (n + 1)) : l.stepApp j ≫ p.app j.obj = b.app j.obj := by
  unfold stepApp
  split_ifs with hj
  · exact congr_app l.fac_right ⟨j.obj, hj⟩
  · exact LiftingStep.component_fac_right r j.obj sq _ _ _

lemma stepApp_direct {x y : Lower r (n + 1)} (f : x ⟶ y) (hf : direct f.hom) :
    B.map f.hom ≫ l.stepApp y = l.stepApp x ≫ X.map f.hom := by
  by_cases hy : r.deg y.obj < n
  · have hx : r.deg x.obj < n := lt_of_le_of_lt (r.le₂ f.hom hf) hy
    rw [stepApp, dite_eq_left hy, stepApp, dite_eq_left hx]
    exact l.hom.naturality (ObjectProperty.homMk f.hom : ⟨x.obj, hx⟩ ⟶ ⟨y.obj, hy⟩)
  · by_cases hid : MorphismProperty.identities J f.hom
    · exact naturality_on_lower_identities r (n + 1) l.stepApp f hid
    · have hx : r.deg x.obj < n :=
        lt_of_lt_of_le (r.lt₂ f.hom hf hid) (Nat.le_of_lt_succ y.property)
      rw [stepApp, dite_eq_right hy, stepApp, dite_eq_left hx]
      let q : LatchingIndex r y.obj := ⟨Over.mk f.hom, hf, hid⟩
      exact LiftingStep.incoming r y.obj sq (l.restrictAt y.obj _)
        (l.restrictAt_fac_left y.obj _) (l.restrictAt_fac_right y.obj _) q

lemma stepApp_inverse {x y : Lower r (n + 1)} (f : x ⟶ y) (hf : inverse f.hom) :
    B.map f.hom ≫ l.stepApp y = l.stepApp x ≫ X.map f.hom := by
  by_cases hx : r.deg x.obj < n
  · have hy : r.deg y.obj < n := lt_of_le_of_lt (r.le₁ f.hom hf) hx
    rw [stepApp, dite_eq_left hy, stepApp, dite_eq_left hx]
    exact l.hom.naturality (ObjectProperty.homMk f.hom : ⟨x.obj, hx⟩ ⟶ ⟨y.obj, hy⟩)
  · by_cases hid : MorphismProperty.identities J f.hom
    · exact naturality_on_lower_identities r (n + 1) l.stepApp f hid
    · have hy : r.deg y.obj < n :=
        lt_of_lt_of_le (r.lt₁ f.hom hf hid) (Nat.le_of_lt_succ x.property)
      rw [stepApp, dite_eq_left hy, stepApp, dite_eq_right hx]
      let q : MatchingIndex r x.obj := ⟨Under.mk f.hom, hf, hid⟩
      exact (LiftingStep.outgoing r x.obj sq (l.restrictAt x.obj _)
        (l.restrictAt_fac_left x.obj _) (l.restrictAt_fac_right x.obj _) q).symm

def successor : LiftBelow r sq (n + 1) where
  hom := natTransOnLowerOfReedy r (n + 1) l.stepApp l.stepApp_inverse l.stepApp_direct
  fac_left := by
    apply NatTrans.ext
    funext j
    exact l.stepApp_fac_left j
  fac_right := by
    apply NatTrans.ext
    funext j
    exact l.stepApp_fac_right j

lemma successor_app_old (j : J) (hj : r.deg j < n) :
    l.successor.hom.app ⟨j, lt_trans hj (Nat.lt_succ_self n)⟩ = l.hom.app ⟨j, hj⟩ := by
  change l.stepApp _ = _
  exact dite_eq_left hj

end SerrePositivity.Reedy.LiftBelow
