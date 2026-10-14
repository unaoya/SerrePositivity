module

public import SerrePositivity.BhattScholze.RootedTensorBaseChangeSurjectivity
public import SerrePositivity.BhattScholze.TensorResidueBaseChangeComparison
public import SerrePositivity.BhattScholze.PerfectoidizationSurjectivityDescent
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed

/-! # B4-5：根付き完全忠実平坦perfectoid拡大からの全射性降下

Witt余積・通常mod p比較・G1を合成する。拡大の存在は仮定として明示する。
André引用を使わずに、任意の拡大データに相対的な公開定理を証明する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {R S C T : Type u}
variable [CommRing R] [CommRing S] [CommRing C] [CommRing T]
variable [Algebra R S] [Algebra R C] [Algebra R T]

/-- 根付き核を持つp完全忠実平坦perfectoid拡大があれば、導来p完備な全射商の
任意perfectoid化は全射。p正則性・有限性・古典的完備性を新しく仮定しない。 -/
theorem surjective_of_isPerfectoidization_of_rootedPerfectoidBaseChange
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (ρ : RingHom.ker
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = (s : T)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) : Function.Surjective f := by
  have hmod := surjective_modP_tensorMap_of_rootedPerfectoidBaseChange p hR hT hq
    ρ hρ0 hρ f hf
  have hres := surjective_principalResidueTensor_of_modP_tensorMap p R S T f hmod
  exact surjective_of_isPerfectoidization_of_residue_baseChange f hf hS hflat hres

/-- 拡大の各元の両立するp冪根を入力する全射性降下。拡大の存在は結論に含めない。 -/
theorem surjective_of_isPerfectoidization_of_allRootsPerfectoidBaseChange
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (hroots : ∀ a : T, ∃ ρ : ℕ → T, ρ 0 = a ∧ ∀ n, ρ (n + 1) ^ p = ρ n)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) : Function.Surjective f := by
  let J := RingHom.ker (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  have h : ∀ a : J, ∃ ρ : ℕ → T, ρ 0 = (a : T) ∧ ∀ n, ρ (n + 1) ^ p = ρ n :=
    fun a ↦ hroots a
  choose ρ hρ0 hρ using h
  exact surjective_of_isPerfectoidization_of_rootedPerfectoidBaseChange hR hT hq
    hS hflat ρ hρ0 hρ f hf

/-- 拡大が整代数的閉なら既存の根の補題で必要な根を供給できる。
完全忠実平坦perfectoidな整代数的閉拡大の存在は依然として入力。 -/
theorem surjective_of_isPerfectoidization_of_aicPerfectoidBaseChange
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (haic : IsAbsolutelyIntegrallyClosed T)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) : Function.Surjective f := by
  exact surjective_of_isPerfectoidization_of_allRootsPerfectoidBaseChange hR hT hq hS hflat
    (fun a ↦ haic.exists_compatible_pow_roots (Fact.out : p.Prime).pos a) f hf

end SerrePositivity.BhattScholze
