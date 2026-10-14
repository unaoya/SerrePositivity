module

public import SerrePositivity.BhattScholze.RootedKernelSurjectivity
public import SerrePositivity.BhattScholze.PerfectoidizationBaseChange

/-! # B4-5：根付き底変換後の全射性と標準mod pテンソル射

全射商の通常底変換の標準射を、根を持つ実際の核の補題へ接続する。
根付き拡大の存在・忠実平坦性・最終降下は別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {R S C T E : Type u} [CommRing R] [CommRing S] [CommRing C]
variable [CommRing T] [CommRing E] [Algebra R S] [Algebra R C] [Algebra R T]

/-- 全射商を底変換した核が根を持てば、底変換したperfectoid化の合成射は全射。
商の完備性・有限生成性・p正則性を要求しない。 -/
theorem surjective_perfectoidizationTensorBaseChangeMap_of_rootedKernel
    (p : ℕ) [Fact p.Prime] (hT : IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (ρ : RingHom.ker
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = (s : T)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (F : C ⊗[R] T →+* E) (hF : IsPerfectoidization p F) :
    Function.Surjective (perfectoidizationTensorBaseChangeMap f F) := by
  exact surjective_of_isPerfectoidization_of_rootedKernel hT
    (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
    (Algebra.TensorProduct.includeRight_surjective T hq) ρ hρ0 hρ
    (perfectoidizationTensorBaseChangeMap f F)
    (perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf F hF)

/-- 同じ根付き入力とFの標準mod p比較から、通常テンソル射のmod p全射性を得る。
これをG1の剰余テンソル射へ運ぶ図式と忠実平坦降下は別工程。 -/
theorem surjective_modP_tensorMap_of_rootedKernel
    (p : ℕ) [Fact p.Prime] (hT : IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (ρ : RingHom.ker
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = (s : T)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (F : C ⊗[R] T →+* E) (hF : IsPerfectoidization p F)
    (hbij : Function.Bijective (modPMap p F)) :
    Function.Surjective
      (modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom) := by
  have hsurj := surjective_perfectoidizationTensorBaseChangeMap_of_rootedKernel p
    hT hq ρ hρ0 hρ f hf F hF
  intro y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := hsurj (F c)
  refine ⟨Ideal.Quotient.mk _ x, hbij.injective ?_⟩
  change Ideal.Quotient.mk (Ideal.span {(p : E)})
    (F (Algebra.TensorProduct.map f (AlgHom.id R T) x)) =
      Ideal.Quotient.mk (Ideal.span {(p : E)}) (F c)
  exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : E)})) hx

/-- 任意perfectoid基底と根付き核を持つperfectoid拡大に対し、
標準通常テンソル射のmod pは全射。具体的Witt余積の存在と比較を内部で供給する。 -/
theorem surjective_modP_tensorMap_of_rootedPerfectoidBaseChange
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hT : IsIntegralPerfectoid T p) (hq : Function.Surjective (algebraMap R S))
    (ρ : RingHom.ker
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = (s : T)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    Function.Surjective
      (modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom) := by
  obtain ⟨E, hE, F, hF, hbij, _⟩ := exists_perfectoidizationTensorBaseChange p hR hT f hf
  exact surjective_modP_tensorMap_of_rootedKernel p hT hq ρ hρ0 hρ f hf F hF hbij

end SerrePositivity.BhattScholze
