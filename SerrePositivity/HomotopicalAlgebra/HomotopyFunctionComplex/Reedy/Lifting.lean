module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LiftSuccessor

/-! # Global lifting from relative Reedy lifting properties

For any natural-number graded Reedy category, the compatible sequence of
lifts on degree restrictions yields one natural transformation on the whole
category. No objectwise choice of unrelated lifts is substituted for it.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.Lifting
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {A B X Y : J ⥤ C} {i : A ⟶ B} {p : X ⟶ Y}
  [∀ j, HasLiftingProperty (relativeLatchingMap r j i) (relativeMatchingMap r j p)]
  {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a i p b)

def tower : (n : ℕ) → LiftBelow r sq n
  | 0 => LiftBelow.zero r sq
  | n + 1 => (tower n).successor

lemma tower_app_mono {n m : ℕ} (hnm : n ≤ m) (j : J) (hj : r.deg j < n) :
    (tower r sq m).hom.app ⟨j, lt_of_lt_of_le hj hnm⟩ = (tower r sq n).hom.app ⟨j, hj⟩ := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    exact ((tower r sq m).successor_app_old j (lt_of_lt_of_le hj hnm)).trans ih

abbrev app (j : J) : B.obj j ⟶ X.obj j :=
  (tower r sq (r.deg j + 1)).hom.app ⟨j, Nat.lt_succ_self _⟩

lemma app_eq_tower (n : ℕ) (j : J) (hj : r.deg j < n) :
    app r sq j = (tower r sq n).hom.app ⟨j, hj⟩ :=
  (tower_app_mono r sq (Nat.succ_le_of_lt hj) j (Nat.lt_succ_self _)).symm

lemma naturality {j k : J} (f : j ⟶ k) :
    B.map f ≫ app r sq k = app r sq j ≫ X.map f := by
  let n := max (r.deg j) (r.deg k) + 1
  have hj : r.deg j < n := lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)
  have hk : r.deg k < n := lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)
  rw [app_eq_tower r sq n j hj, app_eq_tower r sq n k hk]
  exact (tower r sq n).hom.naturality (ObjectProperty.homMk f : ⟨j, hj⟩ ⟶ ⟨k, hk⟩)

def lift : B ⟶ X where
  app := app r sq
  naturality _ _ f := naturality r sq f

lemma fac_left : i ≫ lift r sq = a := by
  apply NatTrans.ext
  funext j
  exact congr_app (tower r sq (r.deg j + 1)).fac_left ⟨j, Nat.lt_succ_self _⟩

lemma fac_right : lift r sq ≫ p = b := by
  apply NatTrans.ext
  funext j
  exact congr_app (tower r sq (r.deg j + 1)).fac_right ⟨j, Nat.lt_succ_self _⟩

def liftStruct : sq.LiftStruct where
  l := lift r sq
  fac_left := fac_left r sq
  fac_right := fac_right r sq

include r in
lemma hasLiftingProperty : HasLiftingProperty i p where
  sq_hasLift sq := CommSq.HasLift.mk' (liftStruct r sq)

end SerrePositivity.Reedy.Lifting
