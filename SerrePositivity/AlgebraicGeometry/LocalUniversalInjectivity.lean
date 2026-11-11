module

public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：極大点で局所化した写像の普遍単射性から、もとの写像の普遍単射性を得る。
方針：試験加群を局所化し、二段階のテンソル積を一段階にして極大点で単射性を判定する。
規約：加群には有限性を仮定しない。
使われ方：各ファイバーの生成点で得た単射性を、余核による帰納に渡す。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct
open TensorProduct

/--
概要：すべての極大イデアルで局所化した後に普遍単射なら、もとの写像も普遍単射。
方針：テンソル積と局所化の比較を使い、テンソルした写像の単射性を極大点で判定する。
規約：局所化した写像は局所化環とのテンソル積で表す。
使われ方：Stacks 0815 の余核による次元帰納。
-/
theorem lTensor_injective_of_lTensor_baseChange_atMaximal
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (h : ∀ (P : Ideal R) [P.IsMaximal] (Q : Type (max u x)) [AddCommGroup Q]
      [Module (Localization.AtPrime P) Q],
      Function.Injective ((f.baseChange (Localization.AtPrime P)).lTensor Q))
    (X : Type x) [AddCommGroup X] [Module R X] :
    Function.Injective (f.lTensor X) := by
  refine injective_of_isLocalized_maximal
    (fun P _ => LocalizedModule P.primeCompl X ⊗[R] M)
    (fun P _ => AlgebraTensorModule.rTensor R M (LocalizedModule.mkLinearMap P.primeCompl X))
    (fun P _ => LocalizedModule P.primeCompl X ⊗[R] N)
    (fun P _ => AlgebraTensorModule.rTensor R N (LocalizedModule.mkLinearMap P.primeCompl X))
    (f.lTensor X) ?_
  intro P hP
  let S := Localization.AtPrime P
  let Q := LocalizedModule P.primeCompl X
  let j := LocalizedModule.mkLinearMap P.primeCompl X
  change Function.Injective (IsLocalizedModule.map P.primeCompl
    (AlgebraTensorModule.rTensor R M j) (AlgebraTensorModule.rTensor R N j)
    (AlgebraTensorModule.lTensor R X f))
  rw [IsLocalizedModule.map_lTensor]
  let eM := AlgebraTensorModule.cancelBaseChange R S S Q M
  let eN := AlgebraTensorModule.cancelBaseChange R S S Q N
  change Function.Injective (AlgebraTensorModule.lTensor S Q f)
  have hinj : Function.Injective ((AlgebraTensorModule.lTensor S Q f).comp eM.toLinearMap) := by
    rw [AlgebraTensorModule.lTensor_comp_cancelBaseChange]
    exact eN.injective.comp (h P Q)
  intro x y hxy
  apply eM.symm.injective
  apply hinj
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hxy

/--
概要：普遍単射な写像の標的が平坦なら、余核も平坦。
方針：任意の部分加群への包含とのテンソルが単射であることを、二つの右完全列から得る。
規約：余核を写像の値域による商加群で表す。
使われ方：元の加群が平坦な許容開で、帰納に渡す余核も平坦であること。
-/
theorem flat_cokernel_of_lTensor_injective
    {R : Type u} {M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (hf : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q], Function.Injective (f.lTensor Q)) :
    Module.Flat R (N ⧸ LinearMap.range f) := by
  apply Module.Flat.iff_lTensor_injectiveₛ.mpr
  intro Q _ _ I
  let : AddCommGroup Q := Module.addCommMonoidToAddCommGroup R
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := f) (f₂ := (LinearMap.range f).mkQ) (g₁ := I.subtype) (g₂ := I.mkQ)
    f.exact_map_mkQ_range (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective _)
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp (hf (Q ⧸ I)))
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)

end SerrePositivity.AlgebraicGeometry
