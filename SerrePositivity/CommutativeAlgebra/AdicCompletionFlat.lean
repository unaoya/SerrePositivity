module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionTensor
public import SerrePositivity.CommutativeAlgebra.AdicCompletionScalarRestriction
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Noether 基底上の平坦加群の完備化の平坦性

有限イデアルの包含を平坦加群とテンソルして完備化し、
自然な比較同型で完備化した加群とのテンソルの単射性へ移す。
完備化の平坦性を比較同型の証明の仮定にしない。
-/

@[expose] public section
universe u
namespace SerrePositivity

/-- Noether 環上の平坦加群のイデアル進完備化は、同じ基底環上で平坦。
加群の有限性や前完備性は不要。 -/
theorem flat_adicCompletion_of_flat
    {A P : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup P] [Module A P] [Module.Flat A P] (I : Ideal A) :
    Module.Flat A (AdicCompletion I P) := by
  apply ((Module.Flat.tfae_equational_criterion A (AdicCompletion I P)).out 1 2).mpr
  intro J
  have hinj := (adicCompletion_rTensor_injective_of_finite I J.subtype
    (Submodule.injective_subtype J) (P := P)).comp
    (adicCompletionTensorComparison_injective I J P)
  change Function.Injective ((AdicCompletion.map I (J.subtype.rTensor P)).restrictScalars A ∘ₗ
    adicCompletionTensorComparison I J P) at hinj
  rw [adicCompletionTensorComparison_natural] at hinj
  exact Function.Injective.of_comp hinj

/-- Noether 基底上の平坦代数を、基底から拡張したイデアルで完備化しても基底上平坦。
代数 S 自身の Noether 性・有限性・局所性は不要。 -/
theorem flat_adicCompletion_algebra_of_flat
    {A S : Type u} [CommRing A] [IsNoetherianRing A]
    [CommRing S] [Algebra A S] [Module.Flat A S] (I : Ideal A) :
    Module.Flat A (AdicCompletion (I.map (algebraMap A S)) S) :=
  (Module.Flat.equiv_iff (adicCompletionScalarRestrictionEquiv (S := S) (M := S) I)).mpr
    (flat_adicCompletion_of_flat I)

end SerrePositivity
