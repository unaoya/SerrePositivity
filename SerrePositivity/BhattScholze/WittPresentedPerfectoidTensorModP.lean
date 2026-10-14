module

public import SerrePositivity.BhattScholze.WittPresentedPerfectoidTensor
public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality

/-! # B4-5：全p完備試験環への普遍性からの標準mod p比較

pが零の試験環は自動的にp完備であることを使う。
通常テンソルの標準射のmod pが同型であることを証明する。
導来テンソルの比較には置換しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct

private theorem modP_bijective_of_completeUniversal (p : ℕ) [Fact p.Prime]
    {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
    (hU : ∀ (D : Type u) [CommRing D], IsAdicComplete (Ideal.span {(p : D)}) D →
      ∀ g : A →+* D, ∃! L : C →+* D, L.comp f = g) :
    Function.Bijective (modPMap p f) := by
  let qA := Ideal.Quotient.mk (Ideal.span {(p : A)})
  let qC := Ideal.Quotient.mk (Ideal.span {(p : C)})
  have hpA : (p : ModP A p) = 0 := by
    rw [← map_natCast qA]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hpC : (p : ModP C p) = 0 := by
    rw [← map_natCast qC]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hcA : IsAdicComplete (Ideal.span {(p : ModP A p)}) (ModP A p) := by
    rw [hpA, Ideal.span_singleton_zero]
    infer_instance
  have hcC : IsAdicComplete (Ideal.span {(p : ModP C p)}) (ModP C p) := by
    rw [hpC, Ideal.span_singleton_zero]
    infer_instance
  obtain ⟨r, hr, _⟩ := hU (ModP A p) hcA qA
  have hk : Ideal.span {(p : C)} ≤ RingHom.ker r := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change r (p : C) = 0
    rw [map_natCast, hpA]
  let g := Ideal.Quotient.lift (Ideal.span {(p : C)}) r (fun _ hx ↦ hk hx)
  have hl : Function.LeftInverse g (modPMap p f) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact RingHom.congr_fun hr a
  have hm : ((modPMap p f).comp r).comp f = qC.comp f := by
    apply RingHom.ext
    intro a
    change modPMap p f (r (f a)) = qC (f a)
    have ha := RingHom.congr_fun hr a
    change r (f a) = qA a at ha
    rw [ha]
    rfl
  have he : (modPMap p f).comp r = qC :=
    (hU (ModP C p) hcC (qC.comp f)).unique hm rfl
  have hright : Function.RightInverse g (modPMap p f) := by
    intro x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact RingHom.congr_fun he c
  exact ⟨hl.injective, hright.surjective⟩

variable (p : ℕ) [Fact p.Prime]
variable (kR kS kT : Type u) [CommRing kR] [CommRing kS] [CommRing kT]
variable [Algebra kR kS] [Algebra kR kT]
variable [CharP kR p] [CharP kS p] [CharP kT p]
variable [PerfectRing kR p] [PerfectRing kS p] [PerfectRing kT p]
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- 表示付き通常テンソルからのperfectoid化は、標準mod p射が全単射。
一般pねじれ入力と零環の係数余積も含む。 -/
theorem exists_wittPresentedTensorPerfectoidization_modP
    (d : WittVector p kR) (hd : (wittDeltaStructure p kR).IsDistinguished d)
    (θ : WittVector p kR →+* R) (hθ : Function.Surjective θ)
    (eS : (WittVector p kS ⧸ Ideal.span {WittVector.map (algebraMap kR kS) d}) ≃+* S)
    (eT : (WittVector p kT ⧸ Ideal.span {WittVector.map (algebraMap kR kT) d}) ≃+* T)
    (hS : (eS.toRingHom.comp (Ideal.Quotient.mk _)).comp
      (WittVector.map (algebraMap kR kS)) = (algebraMap R S).comp θ)
    (hT : (eT.toRingHom.comp (Ideal.Quotient.mk _)).comp
      (WittVector.map (algebraMap kR kT)) = (algebraMap R T).comp θ) :
    ∃ F : S ⊗[R] T →+* WittCoefficientPushout p kR kS kT d,
      F.comp (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom =
        (wittCoefficientPushoutLeft p kR kS kT d).comp eS.symm.toRingHom ∧
      F.comp (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom =
        (wittCoefficientPushoutRight p kR kS kT d).comp eT.symm.toRingHom ∧
      IsPerfectoidization p F ∧ Function.Bijective (modPMap p F) := by
  obtain ⟨F, hFS, hFT, hE, hU⟩ := exists_wittPresentedTensorCompletion p kR kS kT
    d hd θ hθ eS eT hS hT
  refine ⟨F, hFS, hFT, ⟨hE, ?_⟩, modP_bijective_of_completeUniversal p F hU⟩
  intro D _ hD g
  exact hU D (hD.isAdicComplete D p) g

end SerrePositivity.BhattScholze
