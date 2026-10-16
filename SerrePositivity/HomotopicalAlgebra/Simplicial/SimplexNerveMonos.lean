module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # The actual simplex-nerve functor preserves monomorphisms

The index chain is unchanged and the original first label is sent by
the original injective component. No model structure is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SimplexNerve
variable {X Y : SSet.{v}} (f : X ⟶ Y) [Mono f]

lemma degreeLabels_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((degreeLabels n).map f) := by
  change Function.Injective (Sigma.map (fun δ : Chains n => δ)
    (fun δ x => f.app (δ.obj 0) x))
  exact Function.Injective.sigma_map Function.injective_id
    (fun δ => (mono_iff_injective (f.app (δ.obj 0))).mp inferInstance)

lemma map_injective (n : SimplexCategoryᵒᵖ) : Function.Injective ((functor.map f).app n) := by
  intro c d h
  apply (chainEquiv X n).injective
  apply degreeLabels_injective f n
  exact congrArg (chainEquiv Y n) h

instance map_mono : Mono (functor.map f) :=
  (NatTrans.mono_iff_mono_app _).mpr (fun n =>
    (mono_iff_injective _).mpr (map_injective f n))

instance preservesMonomorphisms : functor.{v}.PreservesMonomorphisms where
  preserves _ _ := inferInstance

end SerrePositivity.SimplicialModel.SimplexNerve
