module

public import SerrePositivity.BhattScholze.PerfectoidWittPushout
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationUniqueness
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationCompletion

/-! # B4-5：Witt商表示を持つ環のテンソルからのperfectoid化

共通のWitt基底写像に沿う商表示と図式を明示して入力する。
標準Fontaine商表示をこの入口へ供給する工程とmod p比較は別に残る。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]
variable (kR kS kT : Type u) [CommRing kR] [CommRing kS] [CommRing kT]
variable [Algebra kR kS] [Algebra kR kT]
variable [CharP kR p] [CharP kS p] [CharP kT p]
variable [PerfectRing kR p] [PerfectRing kS p] [PerfectRing kT p]
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- 共通のdistinguished元によるWitt商表示がある環のテンソルは、
具体的なWitt係数余積への射は全p完備環への射を一意に経由する。零環も含む。 -/
theorem exists_wittPresentedTensorCompletion
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
      IsIntegralPerfectoid (WittCoefficientPushout p kR kS kT d) p ∧
      ∀ (D : Type u) [CommRing D], IsAdicComplete (Ideal.span {(p : D)}) D →
        ∀ g : S ⊗[R] T →+* D, ∃! L : WittCoefficientPushout p kR kS kT d →+* D,
          L.comp F = g := by
  let E := WittCoefficientPushout p kR kS kT d
  let iS := (wittCoefficientPushoutLeft p kR kS kT d).comp eS.symm.toRingHom
  let iT := (wittCoefficientPushoutRight p kR kS kT d).comp eT.symm.toRingHom
  have hi (r : R) : iS (algebraMap R S r) = iT (algebraMap R T r) := by
    obtain ⟨x, rfl⟩ := hθ r
    have hxS := RingHom.congr_fun hS x
    have hxT := RingHom.congr_fun hT x
    change eS (Ideal.Quotient.mk _ (WittVector.map (algebraMap kR kS) x)) =
      algebraMap R S (θ x) at hxS
    change eT (Ideal.Quotient.mk _ (WittVector.map (algebraMap kR kT) x)) =
      algebraMap R T (θ x) at hxT
    change wittCoefficientPushoutLeft p kR kS kT d (eS.symm _) =
      wittCoefficientPushoutRight p kR kS kT d (eT.symm _)
    rw [← hxS, ← hxT, eS.symm_apply_apply, eT.symm_apply_apply]
    exact RingHom.congr_fun (wittCoefficientPushout_base_agreement p kR kS kT d) x
  let F := coefficientTensorLift iS iT hi
  have hFS : F.comp
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom = iS := by
    ext s
    change coefficientTensorLift iS iT hi (s ⊗ₜ[R] (1 : T)) = iS s
    rw [coefficientTensorLift_tmul, map_one, mul_one]
  have hFT : F.comp
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom = iT := by
    ext t
    change coefficientTensorLift iS iT hi ((1 : S) ⊗ₜ[R] t) = iT t
    rw [coefficientTensorLift_tmul, map_one, one_mul]
  refine ⟨F, hFS, hFT, wittCoefficientPushout_isIntegralPerfectoid p kR kS kT d hd, ?_⟩
  intro D _ hD g
  let := hD
  let jS := (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom
  let jT := (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  let fS := (g.comp jS).comp eS.toRingHom
  let fT := (g.comp jT).comp eT.toRingHom
  have hf : (fS.comp (Ideal.Quotient.mk _)).comp (WittVector.map (algebraMap kR kS)) =
      (fT.comp (Ideal.Quotient.mk _)).comp (WittVector.map (algebraMap kR kT)) := by
    ext x
    change g (jS (eS (Ideal.Quotient.mk _ (WittVector.map (algebraMap kR kS) x)))) =
      g (jT (eT (Ideal.Quotient.mk _ (WittVector.map (algebraMap kR kT) x))))
    have hxS := RingHom.congr_fun hS x
    have hxT := RingHom.congr_fun hT x
    change eS (Ideal.Quotient.mk _ (WittVector.map (algebraMap kR kS) x)) =
      algebraMap R S (θ x) at hxS
    change eT (Ideal.Quotient.mk _ (WittVector.map (algebraMap kR kT) x)) =
      algebraMap R T (θ x) at hxT
    rw [hxS, hxT]
    exact congrArg g (((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes
      (θ x)).trans ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes
        (θ x)).symm)
  obtain ⟨L, ⟨hLS, hLT⟩, huniq⟩ := existsUnique_wittCoefficientPushoutLift p kR kS kT d
    fS fT hf
  have hLiS (s : S) : L (iS s) = g (jS s) := by
    have hx := RingHom.congr_fun hLS (eS.symm s)
    change L (wittCoefficientPushoutLeft p kR kS kT d (eS.symm s)) =
      g (jS (eS (eS.symm s))) at hx
    rw [eS.apply_symm_apply] at hx
    exact hx
  have hLiT (t : T) : L (iT t) = g (jT t) := by
    have hx := RingHom.congr_fun hLT (eT.symm t)
    change L (wittCoefficientPushoutRight p kR kS kT d (eT.symm t)) =
      g (jT (eT (eT.symm t))) at hx
    rw [eT.apply_symm_apply] at hx
    exact hx
  have hLF : L.comp F = g := by
    apply RingHom.ext
    intro x
    refine TensorProduct.inductionOn x (fun s t ↦ ?_) (fun x y hx hy ↦ ?_)
    · change L (coefficientTensorLift iS iT hi (s ⊗ₜ[R] t)) = g (s ⊗ₜ[R] t)
      rw [coefficientTensorLift_tmul, map_mul, hLiS, hLiT, ← map_mul]
      congr 1
      change (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) = s ⊗ₜ[R] t
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · simp only [map_add, hx, hy]
  refine ⟨L, hLF, ?_⟩
  intro M hM
  apply huniq
  constructor
  · apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun hM (jS (eS x))
    have he := RingHom.congr_fun hFS (eS x)
    change F (jS (eS x)) = iS (eS x) at he
    change M (F (jS (eS x))) = g (jS (eS x)) at hx
    rw [he] at hx
    change M (wittCoefficientPushoutLeft p kR kS kT d (eS.symm (eS x))) =
      g (jS (eS x)) at hx
    rw [eS.symm_apply_apply] at hx
    exact hx
  · apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun hM (jT (eT x))
    have he := RingHom.congr_fun hFT (eT x)
    change F (jT (eT x)) = iT (eT x) at he
    change M (F (jT (eT x))) = g (jT (eT x)) at hx
    rw [he] at hx
    change M (wittCoefficientPushoutRight p kR kS kT d (eT.symm (eT x))) =
      g (jT (eT x)) at hx
    rw [eT.symm_apply_apply] at hx
    exact hx

/-- 表示付き通常テンソルからの具体的なWitt余積への射はperfectoid化。 -/
theorem exists_wittPresentedTensorPerfectoidization
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
      IsPerfectoidization p F := by
  obtain ⟨F, hFS, hFT, hE, hU⟩ := exists_wittPresentedTensorCompletion p kR kS kT
    d hd θ hθ eS eT hS hT
  refine ⟨F, hFS, hFT, hE, ?_⟩
  intro D _ hD g
  exact hU D (hD.isAdicComplete D p) g

end SerrePositivity.BhattScholze
