module

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Reflection
public import SerrePositivity.HomologicalAlgebra.DerivedModuleCone
public import SerrePositivity.CommutativeAlgebra.TensorProduct.BaseChange
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # integral perfectoid 環の導来完備性

## 概要

integral perfectoid な代数は、定義の古典的な完備性から、任意の係数環への制限について導来 p 完備である（`IsIntegralPerfectoid.isModuleComplete_algebra`）。integral perfectoid な `R` 上の有限・有限表示な代数の導来 p 完備性（`isModuleComplete_finitePresentation_of_integralPerfectoid`）、perfectoid な終域への写像の錐の導来 p 完備性（`cone_isComplete_of_integralPerfectoid_target`）、perfectoid 環の族の直積とその基底変更・テンソル積の導来 p 完備性（`pi_isModuleComplete_of_integralPerfectoid` ほか）を与える。

## 方針

有限表示な加群の導来完備性と、導来完備加群の直積・錐での閉性に帰着する。

## 規約

ねじれのなさや有界なねじれは要らない。旧 `CommutativeAlgebra/PerfectoidDerivedComplete`（2a で移した）と、CLMST の Prop 2.4.7 の証明の `Prop247Cone`・`Prop247RankCompleteness` の一般部分（2b で下ろし、内容の名前に改めた）。

## 使われ方

BhattScholze、CLMST（Prop 2.4.7）。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open DerivedCompletion

/-- An integral perfectoid ring, including the zero ring, is derived p-complete. -/
lemma IsIntegralPerfectoid.isModuleComplete
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    (hS : IsIntegralPerfectoid S p) :
    IsModuleComplete S (p : S) (ModuleCat.of S S) := by
  rcases hS with hS | ⟨_, hc, _⟩
  · let : Subsingleton S := hS
    exact isModuleComplete_of_pow_smul_zero S (p : S) _ 0
      (fun _ => Subsingleton.elim _ _)
  · let := hc
    exact isModuleComplete_of_isAdicComplete S (p : S) (ModuleCat.of S S)

/-- The original algebra action of any base ring gives a derived p-complete
coefficient module. -/
lemma IsIntegralPerfectoid.isModuleComplete_algebra
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsModuleComplete R (p : R) (ModuleCat.of R S) := by
  apply (isModuleComplete_algebraMap_iff R S (p : R) S).mp
  simpa only [map_natCast] using hS.isModuleComplete S p

end SerrePositivity

section IntegralPerfectoidFinitePart

namespace SerrePositivity
open CategoryTheory DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

include hR in
/-- integral perfectoid な `R` 上の有限・有限表示な代数は、`R` の作用について導来 p 完備。 -/
theorem isModuleComplete_finitePresentation_of_integralPerfectoid :
    IsModuleComplete R (p : R) (ModuleCat.of R S) := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  exact isModuleComplete_of_finitePresentation R (p : R)
    (hR.isModuleComplete R p) (ModuleCat.of R S)

include hR in
/-- 任意に指定した perfectoid な終域への実射の錐は導来 p 完備。
普遍対象の存在引用を用いない入口。 -/
theorem cone_isComplete_of_integralPerfectoid_target
    (P : Type u) [CommRing P] [Algebra R P]
    (hP : IsIntegralPerfectoid P p) (f : S →ₗ[R] P) :
    IsComplete R (p : R) (moduleMapCone R f) := by
  apply isComplete_Q_mappingCone R (p : R) (moduleMapSingle R f)
  · exact isModuleComplete_finitePresentation_of_integralPerfectoid R S p hR
  · exact hP.isModuleComplete_algebra R P p

end SerrePositivity

end IntegralPerfectoidFinitePart

section IntegralPerfectoidProductPart

namespace SerrePositivity
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    {ι : Type} (T : ι → Type u) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (hT : ∀ i, IsIntegralPerfectoid (T i) p)

include R hT

/-- 各実 perfectoid 係数の直積は元の R の作用について導来 p 完備。 -/
theorem pi_isModuleComplete_of_integralPerfectoid :
    IsModuleComplete R (p : R) (ModuleCat.of R ((i : ι) → T i)) :=
  isModuleComplete_pi R (p : R) (fun i => ModuleCat.of R (T i))
    (fun i => (hT i).isModuleComplete_algebra R (T i) p)

/-- 同じ実係数直積は、その環自身の p に関して導来完備。 -/
theorem pi_self_isModuleComplete_of_integralPerfectoid :
    IsModuleComplete ((i : ι) → T i) (p : (i : ι) → T i)
      (ModuleCat.of ((i : ι) → T i) ((i : ι) → T i)) := by
  have h := (isModuleComplete_algebraMap_iff R ((i : ι) → T i) (p : R)
    ((i : ι) → T i)).mpr (pi_isModuleComplete_of_integralPerfectoid R p T hT)
  simpa only [map_natCast] using h

variable (S : Type u) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]

/-- 元の各 Si=Ti⊗R S の実直積は、S の bounded torsion を要求せず導来 p 完備。 -/
theorem pi_baseChange_isModuleComplete_of_integralPerfectoid :
    IsModuleComplete R (p : R) (ModuleCat.of R ((i : ι) → T i ⊗[R] S)) := by
  apply isModuleComplete_pi R (p : R) (fun i => ModuleCat.of R (T i ⊗[R] S))
  intro i
  apply (isModuleComplete_algebraMap_iff R (T i) (p : R) (T i ⊗[R] S)).mp
  simpa only [map_natCast] using isModuleComplete_finitePresentation_of_integralPerfectoid (T i) (T i ⊗[R] S) p (hT i)

/-- 通常 tensor の元の係数直積による底変換も、実直積比較で導来 p 完備。 -/
theorem piTensor_isModuleComplete_of_integralPerfectoid [Finite ι] :
    IsModuleComplete R (p : R) (ModuleCat.of R (((i : ι) → T i) ⊗[R] S)) := by
  let e := (finiteProductBaseChangeEquiv R S T).toLinearEquiv.restrictScalars R
  exact isModuleComplete_of_linearEquiv R (p : R)
    (ModuleCat.of R ((i : ι) → T i ⊗[R] S))
    (ModuleCat.of R (((i : ι) → T i) ⊗[R] S)) e.symm
    (pi_baseChange_isModuleComplete_of_integralPerfectoid R p T hT S)

end SerrePositivity

end IntegralPerfectoidProductPart
