module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedCoproductComposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalLabelCoefficients
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
/-!
概要：始点を保つラベルの有限係数和を、係数加群の直和間の作用へ移す。
方針：始点保存写像の厳密な合成則を線形に延長する。
規約：始点保存を部分型で保持し、始点を変える写像には作用を定めない。
使われ方：Dold–Kan の普遍係数の退化消滅を実 bar の係数作用へ移す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

abbrev DGCoherentBarBasedLabel (m n : ℕ) :=
  {a : (Δ[m] : SSet.{u}) _⦋n⦌ // a 0 = 0}

def dgCoherentBarBasedLabelPush {l m n : ℕ} (f : ⦋m⦌ ⟶ ⦋l⦌)
    (hf : f.toOrderHom 0 = 0) (a : DGCoherentBarBasedLabel.{u} m n) :
    DGCoherentBarBasedLabel.{u} l n :=
  ⟨(SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌) a.val, by
    change f.toOrderHom (a.val 0) = 0
    rw [a.property, hf]⟩

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarBasedCoefficientAction (m n : ℕ) :
    (DGCoherentBarBasedLabel.{u} m n →₀ R) →ₗ[R]
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedCoproduct R D F m ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedCoproduct R D F n) :=
  Finsupp.linearCombination R (fun a : DGCoherentBarBasedLabel.{u} m n =>
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedMap R D F (SSet.stdSimplex.objEquiv a.val) a.property)

lemma dgCoherentBarBasedCoefficientAction_push {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋l⦌) (hf : f.toOrderHom 0 = 0)
    (z : DGCoherentBarBasedLabel.{u} m n →₀ R) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedMap R D F f hf ≫ dgCoherentBarBasedCoefficientAction R D F m n z =
      dgCoherentBarBasedCoefficientAction R D F l n
        (Finsupp.mapDomain (dgCoherentBarBasedLabelPush f hf) z) := by
  have h := Finsupp.lmapDomain_linearCombination R
    (v := fun a : DGCoherentBarBasedLabel.{u} m n =>
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedMap R D F (SSet.stdSimplex.objEquiv a.val) a.property)
    (v' := fun a : DGCoherentBarBasedLabel.{u} l n =>
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedMap R D F (SSet.stdSimplex.objEquiv a.val) a.property)
    (dgCoherentBarBasedLabelPush f hf)
    (CategoryTheory.Linear.leftComp R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedCoproduct R D F n)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedMap R D F f hf)) (fun a => by
        exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedMap_comp R D F f hf
          (SSet.stdSimplex.objEquiv a.val) a.property)
  exact (LinearMap.congr_fun h z).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
