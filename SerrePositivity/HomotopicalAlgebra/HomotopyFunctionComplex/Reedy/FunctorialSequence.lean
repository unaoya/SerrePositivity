module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialSuccessor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationTower

/-! # Coherent functorial factorization families at all natural degrees -/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.FunctorFactorizationSequence
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg)
  {left right : MorphismProperty C} (data : MorphismProperty.FunctorialFactorizationData left right)

def stage : (n : ℕ) → FunctorFactorAt (C := C) r n
  | 0 =>
    { Z := Arrow.leftFunc ⋙ restrictionFunctor r 0
      i := 𝟙 _
      p := restrictedArrowTransformation r 0
      fac := Category.id_comp _
      hi := trivial
      hp := trivial }
  | n + 1 => (FunctorFactorSuccessor.next r hinj data hsurj n (stage n)).factor

abbrev nextStage (n : ℕ) :=
  FunctorFactorSuccessor.next r hinj data hsurj n (stage r hinj hsurj data n)

lemma stage_atArrow (n : ℕ) (φ : Arrow (J ⥤ C)) :
    (stage r hinj hsurj data n).atArrow φ =
      FactorizationSequence.stage r φ.hom hinj hsurj data.factorizationData n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stage, FunctorFactorSuccessor.next_atArrow, ih]
    rfl

lemma stage_succ_atObject (j : J) (φ : Arrow (J ⥤ C)) :
    (stage r hinj hsurj data (r.deg j + 1)).atArrow φ =
      (FactorSuccessor.atObject hinj data.factorizationData j
        ((stage r hinj hsurj data (r.deg j)).atArrow φ)).factor := by
  rw [stage, FunctorFactorSuccessor.next_atArrow, FactorSuccessor.next_atObject]

abbrev pointTower (φ : Arrow (J ⥤ C)) : FactorizationTower r φ.hom where
  diagram :=
    { stage n := (stage r hinj hsurj data n).Z.obj φ
      step n := (nextStage r hinj hsurj data n).restriction.app φ }
  left :=
    { app n := (stage r hinj hsurj data n).i.app φ
      step n := (congr_app (nextStage r hinj hsurj data n).left φ).trans
        (Category.id_comp _).symm }
  right :=
    { app n := (stage r hinj hsurj data n).p.app φ
      step n := (Category.comp_id _).trans
        (congr_app (nextStage r hinj hsurj data n).right φ).symm }
  fac n := congr_app (stage r hinj hsurj data n).fac φ

abbrev towerMap {φ ψ : Arrow (J ⥤ C)} (s : φ ⟶ ψ) :
    DiagramTower.Map (pointTower r hinj hsurj data φ).diagram
      (pointTower r hinj hsurj data ψ).diagram where
  app n := (stage r hinj hsurj data n).Z.map s
  step n := (nextStage r hinj hsurj data n).restriction.hom.naturality s

lemma pointLeft_app (φ : Arrow (J ⥤ C)) (j : J) :
    (pointTower r hinj hsurj data φ).leftMap.app j =
      ((stage r hinj hsurj data (r.deg j + 1)).i.app φ).app ⟨j, Nat.lt_succ_self _⟩ :=
  Category.id_comp _

lemma pointRight_app (φ : Arrow (J ⥤ C)) (j : J) :
    (pointTower r hinj hsurj data φ).rightMap.app j =
      ((stage r hinj hsurj data (r.deg j + 1)).p.app φ).app ⟨j, Nat.lt_succ_self _⟩ :=
  Category.comp_id _

end SerrePositivity.Reedy.FunctorFactorizationSequence
