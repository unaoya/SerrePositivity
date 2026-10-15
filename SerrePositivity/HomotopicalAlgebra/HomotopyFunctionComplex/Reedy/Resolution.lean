module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ComponentClasses
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Actual cofibrant and fibrant resolutions of constant Reedy diagrams

The records contain a diagram, its comparison, the Reedy condition and a
relative trivial comparison. Ordinary existence uses only source model
factorization. No functorial choice is asserted in this module.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ)
  {C : Type u'} [Category.{v'} C] [ModelCategory C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C]

structure CofibrantResolution (X : C) where
  obj : J ⥤ C
  augmentation : obj ⟶ (Functor.const J).obj X
  cofibrant : reedyLeft r (cofibrations C) (initial.to obj)
  trivial : reedyRight r (trivialFibrations C) augmentation

structure FibrantResolution (X : C) where
  obj : J ⥤ C
  coaugmentation : (Functor.const J).obj X ⟶ obj
  fibrant : reedyRight r (fibrations C) (terminal.from obj)
  trivial : reedyLeft r (trivialCofibrations C) coaugmentation

namespace CofibrantResolution
variable {r} {X : C} (q : CofibrantResolution r X)

lemma augmentation_weakEquivalence (j : J) : weakEquivalences C (q.augmentation.app j) :=
  (trivialFibration_app r q.augmentation q.trivial j).2

lemma homotopicallyConstant {j k : J} (f : j ⟶ k) : weakEquivalences C (q.obj.map f) := by
  have h := q.augmentation.naturality f
  change q.obj.map f ≫ q.augmentation.app k = q.augmentation.app j ≫ 𝟙 X at h
  have hc : weakEquivalences C (q.obj.map f ≫ q.augmentation.app k) := by
    exact h.symm ▸ ((Category.comp_id (q.augmentation.app j)).symm ▸
      q.augmentation_weakEquivalence j)
  exact (weakEquivalences C).of_postcomp _ _ (q.augmentation_weakEquivalence k) hc

lemma isCofibrant : letI := categoryWithCofibrations (C := C) r; IsCofibrant q.obj := by
  let := categoryWithCofibrations (C := C) r
  exact ⟨q.cofibrant⟩

lemma isCofibrant_obj (j : J) : IsCofibrant (q.obj.obj j) := by
  have hi : Cofibration ((initial.to q.obj).app j) :=
    ⟨cofibration_app r (initial.to q.obj) q.cofibrant j⟩
  exact (isCofibrant_iff_of_isInitial ((initial.to q.obj).app j)
    (initialIsInitial.isInitialObj ((evaluation J C).obj j) (⊥_ (J ⥤ C)))).mpr hi

def ofFactor (d : MorphismProperty.MapFactorizationData (reedyLeft r (cofibrations C))
    (reedyRight r (trivialFibrations C)) (initial.to ((Functor.const J).obj X))) :
    CofibrantResolution r X where
  obj := d.Z
  augmentation := d.p
  cofibrant := (Subsingleton.elim d.i (initial.to d.Z)) ▸ d.hi
  trivial := d.hp

end CofibrantResolution

namespace FibrantResolution
variable {r} {X : C} (q : FibrantResolution r X)

lemma coaugmentation_weakEquivalence (j : J) : weakEquivalences C (q.coaugmentation.app j) :=
  (trivialCofibration_app r q.coaugmentation q.trivial j).2

lemma homotopicallyConstant {j k : J} (f : j ⟶ k) : weakEquivalences C (q.obj.map f) := by
  have h := q.coaugmentation.naturality f
  change 𝟙 X ≫ q.coaugmentation.app k = q.coaugmentation.app j ≫ q.obj.map f at h
  have hc : weakEquivalences C (q.coaugmentation.app j ≫ q.obj.map f) := by
    exact h ▸ ((Category.id_comp (q.coaugmentation.app k)).symm ▸
      q.coaugmentation_weakEquivalence k)
  exact (weakEquivalences C).of_precomp _ _ (q.coaugmentation_weakEquivalence j) hc

lemma isFibrant : letI := categoryWithFibrations (C := C) r; IsFibrant q.obj := by
  let := categoryWithFibrations (C := C) r
  exact ⟨q.fibrant⟩

lemma isFibrant_obj (j : J) : IsFibrant (q.obj.obj j) := by
  have hp : Fibration ((terminal.from q.obj).app j) :=
    ⟨fibration_app r (terminal.from q.obj) q.fibrant j⟩
  exact (isFibrant_iff_of_isTerminal ((terminal.from q.obj).app j)
    (terminalIsTerminal.isTerminalObj ((evaluation J C).obj j) (⊤_ (J ⥤ C)))).mpr hp

def ofFactor (d : MorphismProperty.MapFactorizationData (reedyLeft r (trivialCofibrations C))
    (reedyRight r (fibrations C)) (terminal.from ((Functor.const J).obj X))) :
    FibrantResolution r X where
  obj := d.Z
  coaugmentation := d.i
  fibrant := (Subsingleton.elim d.p (terminal.from d.Z)) ▸ d.hp
  trivial := d.hi

end FibrantResolution

def cofibrantResolution (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg)
    (X : C) : CofibrantResolution r X := by
  let : MorphismProperty.IsWeakFactorizationSystem
      (reedyLeft r (cofibrations C)) (reedyRight r (trivialFibrations C)) :=
    weakFactorizationSystem r _ _ hinj hsurj
  exact CofibrantResolution.ofFactor (MorphismProperty.factorizationData _ _
    (initial.to ((Functor.const J).obj X)))

def fibrantResolution (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg)
    (X : C) : FibrantResolution r X := by
  let : MorphismProperty.IsWeakFactorizationSystem
      (reedyLeft r (trivialCofibrations C)) (reedyRight r (fibrations C)) :=
    weakFactorizationSystem r _ _ hinj hsurj
  exact FibrantResolution.ofFactor (MorphismProperty.factorizationData _ _
    (terminal.from ((Functor.const J).obj X)))

end SerrePositivity.Reedy
