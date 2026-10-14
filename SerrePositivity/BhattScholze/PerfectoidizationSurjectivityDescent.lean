module

public import SerrePositivity.CommutativeAlgebra.PrincipalAdicFaithfulDescent
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationCompletion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # B4-5：受領G1によるperfectoid化の全射性降下

mod pのテンソル射の全射性を入力とし、既存の忠実平坦降下を適用する。
完備底変換との比較・その射の全射性は別工程の仮定であり、自動とはしない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] principalAdicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {R S C R' : Type u}
variable [CommRing R] [CommRing S] [CommRing C] [CommRing R']
variable [Algebra R S] [Algebra R C] [Algebra R R']

/-- 導来p完備な源のperfectoid化は、p完全忠実平坦拡大後のmod p全射性から全射になる。
通常のR'の忠実平坦性や源のp正則性は要求しない。 -/
theorem surjective_of_isPerfectoidization_of_residue_baseChange
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) R')
    (h : Function.Surjective
      ((principalAdicReductionMap (p : R) f).lTensor
        ((R ⧸ Ideal.span {(p : R)}) ⊗[R] R'))) : Function.Surjective f := by
  have hrec := (DerivedCompletion.isModuleComplete_iff_recurrence_bijective
    S (p : S) (ModuleCat.of S S)).mp hS
  have hpre : IsPrecomplete (Ideal.span {(p : S)}) S :=
    isPrecomplete_of_adicRecurrenceMap_surjective (p : S) hrec.2
  let : IsPrecomplete (Ideal.span {algebraMap R S (p : R)}) S := by
    have he : algebraMap R S (p : R) = (p : S) := map_natCast _ p
    rw [he]
    exact hpre
  let := hf.1.isAdicComplete C p
  let : IsHausdorff (Ideal.span {algebraMap R C (p : R)}) C := by
    have he : algebraMap R C (p : R) = (p : C) := map_natCast _ p
    rw [he]
    infer_instance
  let := hflat.2
  exact surjective_algHom_of_principal_residue_baseChange (p : R) R' f h

end SerrePositivity.BhattScholze
