module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
import SerrePositivity.HomologicalAlgebra.NilpotentModuleFiltration

/-!
# 完全忠実平坦な代数の有限剰余

## 概要
完全忠実平坦な代数は、定義イデアルの冪を含むイデアルで通常の忠実平坦な剰余を与える。

## 方針
試験加群の有限イデアル進フィルトレーションで高次 Tor の消滅を移す。
忠実性は零剰余から有限帰納法で反映する。

## 規約
任意の可換環とイデアル。完備性や有限生成性は仮定しない。

## 使われ方
BS 著者版 Corollary 3.12 (c) の通常の忠実平坦な有限剰余。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity

open CategoryTheory TensorProduct
open scoped TensorProduct

variable {R : Type u} [CommRing R]

/-- イデアル I に関する完全平坦性は I の冪を含むイデアルへ移る。 -/
theorem isCompletelyFlat_of_idealPower_le (I J : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsCompletelyFlat I M)
    (n : ℕ) (hIJ : I ^ n ≤ J) : IsCompletelyFlat J M := by
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff M N).mpr
  intro i hi
  apply moduleProperty_of_idealPower_annihilated I (fun T ↦ Subsingleton (TorModule R i M T))
    _ _ n (ModuleCat.of R N) (fun r hr x ↦ hN r (hIJ hr) x)
  · intro T hT
    exact (isConcentratedInDegreeZero_derivedTensor_iff M T).mp (hM T hT) i hi
  · intro S hS h₁ h₃
    let := hS.mono_f
    let := hS.epi_g
    exact torModule_subsingleton_of_exact M S.f.hom S.g.hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact) i h₁ h₃

private theorem subsingleton_of_residueTensor_of_killed_by_power (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]
    (n : ℕ) (N : Type u) [AddCommGroup N] [Module R N]
    (hN : I ^ n ≤ Module.annihilator R N) (hTensor : Subsingleton (N ⊗[R] M)) :
    Subsingleton N := by
  let P := I • (⊤ : Submodule R N)
  let Q := AdicReduction I N
  let := hTensor
  have : Subsingleton (Q ⊗[R] M) :=
    (LinearMap.rTensor_surjective M P.mkQ_surjective).subsingleton
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) Q M
  have := e.injective.subsingleton
  have hQ : Subsingleton Q := Module.FaithfullyFlat.rTensor_reflects_triviality
    (R ⧸ I) ((R ⧸ I) ⊗[R] M) Q
  have ht : I • (⊤ : Submodule R N) = ⊤ := Submodule.Quotient.subsingleton_iff.mp hQ
  have hp : ∀ k : ℕ, I ^ k • (⊤ : Submodule R N) = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Submodule.mul_smul, ht, ih]
  have hbot : I ^ n • (⊤ : Submodule R N) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.smul_le.mpr
    intro r hr x _
    exact Module.mem_annihilator.mp (hN hr) x
  have htopbot : (⊤ : Submodule R N) = ⊥ := (hp n).symm.trans hbot
  have hz (x : N) : x = 0 := by
    have hx : x ∈ (⊥ : Submodule R N) := by
      rw [← htopbot]
      trivial
    exact hx
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

attribute [local instance] adicQuotientAlgebra

/-- 概要：I 完全忠実平坦な代数の通常剰余は、I の冪を含むイデアルに対して忠実平坦。
方針：有限イデアル進フィルトレーションと通常剰余テンソルの比較を使う。
規約：商のスカラー作用は標準写像。
使われ方：完備な Čech 複体の各有限剰余の忠実平坦性。 -/
theorem faithfullyFlat_algebraQuotient_of_idealPower_le (I J : Ideal R)
    (S : Type u) [CommRing S] [Algebra R S] (hS : IsCompletelyFaithfullyFlat I S)
    (n : ℕ) (hIJ : I ^ n ≤ J) :
    Module.FaithfullyFlat (R ⧸ J) (S ⧸ J.map (algebraMap R S)) := by
  have hSJ : IsCompletelyFlat J S := isCompletelyFlat_of_idealPower_le I J S hS.1 n hIJ
  have hflat := flat_residueTensor_of_completelyFlat J S hSJ
  have hff : Module.FaithfullyFlat (R ⧸ J) ((R ⧸ J) ⊗[R] S) := by
    apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality _ _).mpr
    refine ⟨hflat, ?_⟩
    intro N _ _ hTensor
    let _ : Module R N := Module.compHom N (Ideal.Quotient.mk J)
    let _ : IsScalarTower R (R ⧸ J) N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ J) (R ⧸ J) N S
    let : Subsingleton (N ⊗[R ⧸ J] ((R ⧸ J) ⊗[R] S)) := hTensor
    have hNT : Subsingleton (N ⊗[R] S) := e.surjective.subsingleton
    have hN : I ^ n ≤ Module.annihilator R N := by
      intro r hr
      apply Module.mem_annihilator.mpr
      intro x
      change Ideal.Quotient.mk J r • x = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hr), zero_smul]
    let := hS.2
    exact subsingleton_of_residueTensor_of_killed_by_power I S n N hN hNT
  let := hff
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S J).toLinearEquiv

end SerrePositivity
