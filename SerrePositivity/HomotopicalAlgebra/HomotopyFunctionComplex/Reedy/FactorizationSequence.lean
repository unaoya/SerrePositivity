module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DegreeFactorizationStep
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationTower

/-! # Iterating the actual one-object factorization construction

For a natural-number Reedy degree bijection, each successor step uses the
chosen source factorization of the relative boundary map. The new diagram
and both legs retain the preceding factorization through a specified
restriction isomorphism. Reedy class membership for the glued legs and
functoriality in the input arrow are separate subsequent assertions.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  {F G : J ⥤ C} (τ : F ⟶ G)

abbrev FactorBelow (n : ℕ) := MorphismProperty.MapFactorizationData ⊤ ⊤
  (Functor.whiskerLeft (lowerInclusion r n) τ)

structure FactorSuccessor {n : ℕ} (a : FactorBelow r τ n) where
  factor : FactorBelow r τ (n + 1)
  restriction : lowerMap r (Nat.le_succ n) ⋙ factor.Z ≅ a.Z
  left : Functor.whiskerLeft (lowerMap r (Nat.le_succ n)) factor.i ≫ restriction.hom = a.i
  right : restriction.hom ≫ a.p = Functor.whiskerLeft (lowerMap r (Nat.le_succ n)) factor.p

abbrev lowerSuccToUpper (n : ℕ) : Lower r (n + 1) ⥤ Upper r n :=
  ObjectProperty.ιOfLE (fun _ h ↦ Nat.le_of_lt_succ h)

namespace FactorSuccessor
variable {r τ} (hinj : Function.Injective r.deg)
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {left right : MorphismProperty C}
  (factor : ∀ {A B : C} (f : A ⟶ B), MorphismProperty.MapFactorizationData left right f)

abbrev atObject (j : J) (a : FactorBelow r τ (r.deg j)) : FactorSuccessor r τ a := by
  let q := factor
    (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j τ) a)
  exact
    { factor :=
        { Z := lowerSuccToUpper r (r.deg j) ⋙ DegreeFactorizationStep.middle r j hinj τ a q
          i := Functor.whiskerLeft (lowerSuccToUpper r (r.deg j))
            (DegreeFactorizationStep.leftMap r j hinj τ a q)
          p := Functor.whiskerLeft (lowerSuccToUpper r (r.deg j))
            (DegreeFactorizationStep.rightMap r j hinj τ a q)
          fac := by
            ext x
            exact congr_app (DegreeFactorizationStep.leftMap_rightMap r j hinj τ a q)
              ((lowerSuccToUpper r (r.deg j)).obj x)
          hi := trivial
          hp := trivial }
      restriction := DegreeFactorizationStep.restrictionIso r j hinj τ a q
      left := by
        ext x
        exact congr_app (DegreeFactorizationStep.leftMap_restriction r j hinj τ a q) x
      right := by
        ext x
        exact congr_app (DegreeFactorizationStep.rightMap_restriction r j hinj τ a q) x }

variable (r τ) in
def next (hsurj : Function.Surjective r.deg) (n : ℕ) :
    (a : FactorBelow r τ n) → FactorSuccessor r τ a := by
  rcases Classical.indefiniteDescription _ (hsurj n) with ⟨j, hj⟩
  subst n
  intro a
  exact atObject hinj factor j a


lemma next_atObject (hsurj : Function.Surjective r.deg) (j : J)
    (a : FactorBelow r τ (r.deg j)) :
    next r τ hinj factor hsurj (r.deg j) a = atObject hinj factor j a := by
  unfold next
  generalize Classical.indefiniteDescription (fun k : J ↦ r.deg k = r.deg j)
    (hsurj (r.deg j)) = s
  rcases s with ⟨k, hk⟩
  have hkj : k = j := hinj hk
  subst k
  rfl

end FactorSuccessor

namespace FactorizationSequence
variable (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg)
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {left right : MorphismProperty C}
  (factor : ∀ {A B : C} (f : A ⟶ B), MorphismProperty.MapFactorizationData left right f)

def stage : (n : ℕ) → FactorBelow r τ n
  | 0 =>
    { Z := lowerInclusion r 0 ⋙ F
      i := 𝟙 _
      p := Functor.whiskerLeft (lowerInclusion r 0) τ
      fac := Category.id_comp _
      hi := trivial
      hp := trivial }
  | n + 1 => (FactorSuccessor.next r τ hinj factor hsurj n (stage n)).factor


lemma stage_succ_atObject (j : J) :
    stage r τ hinj hsurj factor (r.deg j + 1) =
      (FactorSuccessor.atObject hinj factor j (stage r τ hinj hsurj factor (r.deg j))).factor := by
  rw [stage, FactorSuccessor.next_atObject]

abbrev diagramTower : DiagramTower r C where
  stage n := (stage r τ hinj hsurj factor n).Z
  step n := (FactorSuccessor.next r τ hinj factor hsurj n
    (stage r τ hinj hsurj factor n)).restriction

abbrev factorizationTower : FactorizationTower r τ where
  diagram := diagramTower r τ hinj hsurj factor
  left :=
    { app n := (stage r τ hinj hsurj factor n).i
      step n := by
        exact (FactorSuccessor.next r τ hinj factor hsurj n
          (stage r τ hinj hsurj factor n)).left.trans (Category.id_comp _).symm }
  right :=
    { app n := (stage r τ hinj hsurj factor n).p
      step n := by
        exact (Category.comp_id _).trans (FactorSuccessor.next r τ hinj factor hsurj n
          (stage r τ hinj hsurj factor n)).right.symm }
  fac n := (stage r τ hinj hsurj factor n).fac

abbrev factorizationData : MorphismProperty.MapFactorizationData ⊤ ⊤ τ :=
  (factorizationTower r τ hinj hsurj factor).factorizationData


abbrev ofHasFactorization [left.HasFactorization right] :
    MorphismProperty.MapFactorizationData ⊤ ⊤ τ :=
  factorizationData r τ hinj hsurj (MorphismProperty.factorizationData left right)

abbrev ofFunctorialData (data : MorphismProperty.FunctorialFactorizationData left right) :
    MorphismProperty.MapFactorizationData ⊤ ⊤ τ :=
  factorizationData r τ hinj hsurj data.factorizationData

end FactorizationSequence
end SerrePositivity.Reedy
