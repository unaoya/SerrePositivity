module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarCommaPresentation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation

/-! # The total-element nerve comparison lands in the original ordinary bar

The actual total-nerve augmentation is composed with the explicit comma
presentation. The previously constructed nerve homotopy now has bar values.
No weak equivalence of an augmentation is assumed or asserted here.
-/

@[expose] public section
universe v u uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarNerveBridge
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev rawBridge : nerve (OrdinaryBarTotalCone.Total R) ⟶ OrdinaryBarEvaluation.bar R :=
  BarConstruction.totalNerveAugmentation OrdinaryResolutionPairs.projection
    OrdinaryResolutionPairs.raw ((RightResolutionMapping.projection (C := C)).obj R)

def bridge : SSet.uliftFunctor.{max u v, max u v}.obj
    (nerve (OrdinaryBarTotalCone.Total R)) ⟶ OrdinaryBarEvaluation.bar R where
  app n := ↾fun x => (rawBridge R).app n x.down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f => f x.down) ((rawBridge R).naturality θ)

/-- The independently constructed actual simplex-nerve map, with its same explicit lift. -/
def simplexAugmentation : SSet.uliftFunctor.{max u v, max u v}.obj
    (nerve (OrdinaryBarTotalCone.Index R)) ⟶ OrdinaryBarEvaluation.bar R where
  app n := ↾fun x => (SimplexNerveAugmentation.augmentation
    (OrdinaryBarEvaluation.bar R)).app n x.down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f => f x.down)
      ((SimplexNerveAugmentation.augmentation (OrdinaryBarEvaluation.bar R)).naturality θ)

variable (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

abbrev firstComposite := OrdinaryBarTotalHomotopy.firstMap R ≫ bridge R
abbrev evaluatedComposite := OrdinaryBarTotalHomotopy.evaluatedMap R a b ≫ bridge R

def homotopy : SSet.Homotopy (firstComposite R) (evaluatedComposite R a b) where
  h := (OrdinaryBarTotalHomotopy.homotopy R a b).h ≫ bridge R
  h₀ := by
    rw [← Category.assoc, (OrdinaryBarTotalHomotopy.homotopy R a b).h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, (OrdinaryBarTotalHomotopy.homotopy R a b).h₁]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma image_eq : L.map (firstComposite R) = L.map (evaluatedComposite R a b) :=
  AnodyneHomotopy.map_homotopy_eq L hL (homotopy R a b)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarNerveBridge
