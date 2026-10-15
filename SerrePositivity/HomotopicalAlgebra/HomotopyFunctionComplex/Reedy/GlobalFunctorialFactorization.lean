module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialSequence

/-! # The actual global functorial factorization from coherent degree families

Squares act by the natural middle maps of the finite families and their
restriction coherence. Gluing produces a functor on the original arrow
category. Both factor maps are natural transformations on that category.
Class membership is attached in `FunctorialFactorizationClasses`.
-/

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

def middleFunctor : Arrow (J ⥤ C) ⥤ (J ⥤ C) where
  obj φ := (pointTower r hinj hsurj data φ).diagram.toFunctor
  map s := (towerMap r hinj hsurj data s).toNatTrans
  map_id φ := by
    apply NatTrans.ext
    funext j
    exact congr_app ((stage r hinj hsurj data (r.deg j + 1)).Z.map_id φ)
      ⟨j, Nat.lt_succ_self _⟩
  map_comp s t := by
    apply NatTrans.ext
    funext j
    exact congr_app ((stage r hinj hsurj data (r.deg j + 1)).Z.map_comp s t)
      ⟨j, Nat.lt_succ_self _⟩

def leftTransformation : Arrow.leftFunc ⟶ middleFunctor r hinj hsurj data where
  app φ := (pointTower r hinj hsurj data φ).leftMap
  naturality φ ψ s := by
    apply NatTrans.ext
    funext j
    change s.left.app j ≫ (pointTower r hinj hsurj data ψ).leftMap.app j =
      (pointTower r hinj hsurj data φ).leftMap.app j ≫
        (towerMap r hinj hsurj data s).toNatTrans.app j
    rw [pointLeft_app, pointLeft_app]
    exact congr_app ((stage r hinj hsurj data (r.deg j + 1)).i.naturality s)
      ⟨j, Nat.lt_succ_self _⟩

def rightTransformation : middleFunctor r hinj hsurj data ⟶ Arrow.rightFunc where
  app φ := (pointTower r hinj hsurj data φ).rightMap
  naturality φ ψ s := by
    apply NatTrans.ext
    funext j
    change (towerMap r hinj hsurj data s).toNatTrans.app j ≫
        (pointTower r hinj hsurj data ψ).rightMap.app j =
      (pointTower r hinj hsurj data φ).rightMap.app j ≫ s.right.app j
    rw [pointRight_app, pointRight_app]
    exact congr_app ((stage r hinj hsurj data (r.deg j + 1)).p.naturality s)
      ⟨j, Nat.lt_succ_self _⟩

abbrev rawFunctorialFactorization : MorphismProperty.FunctorialFactorizationData
    (⊤ : MorphismProperty (J ⥤ C)) ⊤ where
  Z := middleFunctor r hinj hsurj data
  i := leftTransformation r hinj hsurj data
  p := rightTransformation r hinj hsurj data
  fac := by
    apply NatTrans.ext
    funext φ
    exact (pointTower r hinj hsurj data φ).leftMap_rightMap
  hi _ := trivial
  hp _ := trivial

end SerrePositivity.Reedy.FunctorFactorizationSequence
