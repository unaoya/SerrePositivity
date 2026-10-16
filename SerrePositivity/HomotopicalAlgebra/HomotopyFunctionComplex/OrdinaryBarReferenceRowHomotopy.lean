module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint
public import SerrePositivity.CategoryTheory.NerveHomotopyUniverse
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftPadding

/-! # The labelled reference-to-row cone gives an actual bar-valued interval

The row endpoint factors through the original small augmentation on
simplex nerves, followed by the same original rowNerveMap.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

def bridge : SSet.uliftFunctor.{v, max u v}.obj (nerve (OrdinaryBarTotalCone.Total R)) ⟶
    OrdinaryBarEvaluation.bar R where
  app n := ↾fun x => (OrdinaryBarNerveBridge.rawBridge R).app n x.down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f => f x.down) ((OrdinaryBarNerveBridge.rawBridge R).naturality θ)

abbrev fromReference := NerveHomotopyUniverse.map (OrdinaryBarReferenceRows.referenceElements R) ≫
  bridge R
abbrev fromRows := NerveHomotopyUniverse.map (OrdinaryBarReferenceRows.rowElements R) ≫ bridge R

def homotopy : SSet.Homotopy (fromReference R) (fromRows R) :=
  HomotopyClasses.postHomotopy (bridge R)
    (NerveHomotopyUniverse.homotopy (OrdinaryBarReferenceRows.comparison R))

def nerveAugmentation : SSet.uliftFunctor.{max u v, v}.obj
    (nerve (OrdinaryBarReferenceRows.raw R).Elements) ⟶ OrdinaryBarEvaluatedEndpoint.SmallNerve R :=
  SSet.uliftFunctor.{max u v, v}.map ((SimplexNerve.functor.{v}).map
    (OrdinaryBarReferenceRows.augmentation R))

lemma row_factorization : fromRows R =
    nerveAugmentation R ≫ OrdinaryBarEvaluatedEndpoint.rowNerveMap R := rfl

def referenceComposite := SSet.uliftFunctor.{max u v, v}.map
  (SimplexNerve.augmentation.app (OrdinaryBarReferenceRows.raw R)) ≫
    (UniverseLift.paddingIso.{v, u}.app (OrdinaryBarReferenceRows.raw R)).inv ≫
      OrdinaryBarReference.sectionMap R

lemma reference_factorization : fromReference R = referenceComposite R := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply OrdinaryBarFirstEndpoint.chain_ext R _ _
  · apply CategoryTheory.Functor.ext (fun _ => rfl)
  · change (((BarConstruction.TotalNerve.simplex
      (BarConstruction.commaValues OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw
        ((RightResolutionMapping.projection (C := C)).obj R))
      (x.down ⋙ OrdinaryBarReferenceRows.referenceElements R)) ⋙
        BarConstruction.commaElements OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw
          ((RightResolutionMapping.projection (C := C)).obj R) n).obj 0) = _
    rw [Functor.comp_obj, BarConstruction.TotalNerve.first_vertex]
    rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy
