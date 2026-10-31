module

public import SerrePositivity.CLMST.Prop247Cone
public import SerrePositivity.CommutativeAlgebra.TensorProduct.BaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure

/-! # Prop 2.4.7：実 rank 図式の離散な環の導来 p 完備性

指定した perfectoid 係数と、元の有限・有限表示代数から各実頂点の完備性を供給する。
導来環の圏や Cor 8.12 の引き戻しはここでは構成しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    {ι : Type} (T : ι → Type u) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (hT : ∀ i, IsIntegralPerfectoid (T i) p)

include R hT

/-- 各実 perfectoid 係数の直積は元の R の作用について導来 p 完備。 -/
theorem prop247_rankCoefficientProduct_isModuleComplete :
    IsModuleComplete R (p : R) (ModuleCat.of R ((i : ι) → T i)) :=
  isModuleComplete_pi R (p : R) (fun i => ModuleCat.of R (T i))
    (fun i => (hT i).isModuleComplete_algebra R (T i) p)

/-- 同じ実係数直積は、その環自身の p に関して導来完備。 -/
theorem prop247_rankCoefficientProduct_self_isModuleComplete :
    IsModuleComplete ((i : ι) → T i) (p : (i : ι) → T i)
      (ModuleCat.of ((i : ι) → T i) ((i : ι) → T i)) := by
  have h := (isModuleComplete_algebraMap_iff R ((i : ι) → T i) (p : R)
    ((i : ι) → T i)).mpr (prop247_rankCoefficientProduct_isModuleComplete R p T hT)
  simpa only [map_natCast] using h

variable (S : Type u) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]

/-- 元の各 Si=Ti⊗R S の実直積は、S の bounded torsion を要求せず導来 p 完備。 -/
theorem prop247_rankBaseChangeProduct_isModuleComplete :
    IsModuleComplete R (p : R) (ModuleCat.of R ((i : ι) → T i ⊗[R] S)) := by
  apply isModuleComplete_pi R (p : R) (fun i => ModuleCat.of R (T i ⊗[R] S))
  intro i
  apply (isModuleComplete_algebraMap_iff R (T i) (p : R) (T i ⊗[R] S)).mp
  simpa only [map_natCast] using prop247_source_isModuleComplete (T i) (T i ⊗[R] S) p (hT i)

/-- 通常 tensor の元の係数直積による底変換も、実直積比較で導来 p 完備。 -/
theorem prop247_rankCoefficientTensor_isModuleComplete [Finite ι] :
    IsModuleComplete R (p : R) (ModuleCat.of R (((i : ι) → T i) ⊗[R] S)) := by
  let e := (finiteProductBaseChangeEquiv R S T).toLinearEquiv.restrictScalars R
  exact isModuleComplete_of_linearEquiv R (p : R)
    (ModuleCat.of R ((i : ι) → T i ⊗[R] S))
    (ModuleCat.of R (((i : ι) → T i) ⊗[R] S)) e.symm
    (prop247_rankBaseChangeProduct_isModuleComplete R p T hT S)

end SerrePositivity.CLMST
