module

public import SerrePositivity.BhattScholze.Semiperfectoid.TensorBaseChangeKernel
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.RootedPresentationSurjectivity
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationBaseChange
public import SerrePositivity.BhattScholze.Semiperfectoid.TensorResidueBaseChangeComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.PerfectoidizationSurjectivityDescent

/-! # B4-6：元の核の生成族の根だけを持つ拡大からの降下

底変換した核の全元の根や拡大の整代数的閉性を要求しない。
任意の元の核の生成族の像に根を供給する、必要な拡大データを明示する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {R S C T E σ : Type u}
variable [CommRing R] [CommRing S] [CommRing C] [CommRing T] [CommRing E]
variable [Algebra R S] [Algebra R C] [Algebra R T]

/-- 元の核の生成族の像が根を持てば、通常底変換したperfectoid化の合成射は全射。 -/
theorem surjective_perfectoidizationTensorBaseChangeMap_of_rootedGeneratingFamily
    (hT : IsIntegralPerfectoid T p) (hq : Function.Surjective (algebraMap R S))
    (a : σ → R) (ha : RingHom.ker (algebraMap R S) = Ideal.span (Set.range a))
    (ρ : σ → ℕ → T) (hρ0 : ∀ s, ρ s 0 = algebraMap R T (a s))
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (F : C ⊗[R] T →+* E) (hF : IsPerfectoidization p F) :
    Function.Surjective (perfectoidizationTensorBaseChangeMap f F) := by
  exact surjective_of_isPerfectoidization_of_rootedPresentation hT
    (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
    (Algebra.TensorProduct.includeRight_surjective T hq) ρ hρ
    (tensorBaseChangeKernel_eq_rootFamilyZeroIdeal hq a ha ρ hρ0)
    (perfectoidizationTensorBaseChangeMap f F)
    (perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf F hF)

/-- 根付きp完全忠実平坦perfectoid拡大を、元の核の任意の生成族について供給すれば、
導来p完備な全射商の任意perfectoid化は全射。拡大の存在は入力として残る。 -/
theorem surjective_of_isPerfectoidization_of_rootedGeneratingFamilyBaseChange
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (a : σ → R) (ha : RingHom.ker (algebraMap R S) = Ideal.span (Set.range a))
    (ρ : σ → ℕ → T) (hρ0 : ∀ s, ρ s 0 = algebraMap R T (a s))
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) : Function.Surjective f := by
  obtain ⟨E, hE, F, hF, hbij, _⟩ := exists_perfectoidizationTensorBaseChange p hR hT f hf
  have hsurj := surjective_perfectoidizationTensorBaseChangeMap_of_rootedGeneratingFamily
    hT hq a ha ρ hρ0 hρ f hf F hF
  have hmod : Function.Surjective
      (modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom) := by
    intro y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hsurj (F c)
    refine ⟨Ideal.Quotient.mk _ x, hbij.injective ?_⟩
    change Ideal.Quotient.mk (Ideal.span {(p : E)})
      (F (Algebra.TensorProduct.map f (AlgHom.id R T) x)) =
        Ideal.Quotient.mk (Ideal.span {(p : E)}) (F c)
    exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : E)})) hx
  exact surjective_of_isPerfectoidization_of_residue_baseChange f hf hS hflat
    (surjective_principalResidueTensor_of_modP_tensorMap p R S T f hmod)

omit [Algebra R S] [Algebra R C] in
/-- 具体的な全射q:R→Sについて、元の核の各元の像にだけ両立する根を持つ
p完全忠実平坦perfectoid拡大があれば、任意perfectoid化f:S→Cは全射。 -/
theorem surjective_of_isPerfectoidization_of_sourceKernelRoots
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p)
    (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (ρ : RingHom.ker q → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = algebraMap R T (s : R))
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  let : Algebra R S := q.toAlgebra
  let : Algebra R C := (f.comp q).toAlgebra
  let ff : S →ₐ[R] C := { f with commutes' := fun _ ↦ rfl }
  let a : RingHom.ker q → R := fun s ↦ s
  have ha : RingHom.ker (algebraMap R S) = Ideal.span (Set.range a) := by
    change RingHom.ker q = Ideal.span (Set.range a)
    apply le_antisymm
    · intro x hx
      exact Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact s.property
  exact surjective_of_isPerfectoidization_of_rootedGeneratingFamilyBaseChange
    hR hT hq hS hflat a ha ρ hρ0 hρ ff hf

end SerrePositivity.BhattScholze
