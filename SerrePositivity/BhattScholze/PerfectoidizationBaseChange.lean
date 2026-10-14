module

public import SerrePositivity.BhattScholze.PerfectCoefficientTensor
public import SerrePositivity.BhattScholze.PerfectoidTensorPerfectoidization
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationUniqueness

/-! # B4-5：普遍perfectoid化の通常テンソルによる基底変更

共通基底の代数写像を用い、具体的な合成射の普遍性を証明する。
底変換した射の全射性やmod p比較はこの定理の結論に含めない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {R S C T E : Type u} [CommRing R] [CommRing S] [CommRing C]
variable [CommRing T] [CommRing E] [Algebra R S] [Algebra R C] [Algebra R T]

/-- 通常テンソル射と候補への射の合成による、具体的な底変換射。 -/
def perfectoidizationTensorBaseChangeMap (f : S →ₐ[R] C) (F : C ⊗[R] T →+* E) :
    S ⊗[R] T →+* E :=
  F.comp (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom

/-- fとFがperfectoid化なら、具体的な底変換合成射もperfectoid化。
R,S,Tのperfectoid性や完備性をこの形式的な普遍性の補題に仮定しない。 -/
theorem perfectoidizationTensorBaseChangeMap_isPerfectoidization
    (p : ℕ) [Fact p.Prime] (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (F : C ⊗[R] T →+* E) (hF : IsPerfectoidization p F) :
    IsPerfectoidization p (perfectoidizationTensorBaseChangeMap f F) := by
  refine ⟨hF.1, ?_⟩
  intro U _ hU g
  let jS := (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom
  let jT := (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  let iC := (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] T).toRingHom
  let iT := (Algebra.TensorProduct.includeRight : T →ₐ[R] C ⊗[R] T).toRingHom
  obtain ⟨lC, hlC, hluniq⟩ := hf.2 U hU (g.comp jS)
  have hi (r : R) : lC (algebraMap R C r) = (g.comp jT) (algebraMap R T r) := by
    calc
      lC (algebraMap R C r) = lC (f (algebraMap R S r)) := congrArg lC (f.commutes r).symm
      _ = g (jS (algebraMap R S r)) := RingHom.congr_fun hlC _
      _ = g (jT (algebraMap R T r)) := congrArg g
        (((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes r).trans
          ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes r).symm)
  let k := coefficientTensorLift lC (g.comp jT) hi
  obtain ⟨L, hL, huniq⟩ := hF.2 U hU k
  have hLg : L.comp (perfectoidizationTensorBaseChangeMap f F) = g := by
    apply RingHom.ext
    intro x
    refine TensorProduct.inductionOn x (fun s t ↦ ?_) (fun x y hx hy ↦ ?_)
    · change L (F (f s ⊗ₜ[R] t)) = g (s ⊗ₜ[R] t)
      have hx := RingHom.congr_fun hL (f s ⊗ₜ[R] t)
      change L (F (f s ⊗ₜ[R] t)) = coefficientTensorLift lC (g.comp jT) hi
        (f s ⊗ₜ[R] t) at hx
      rw [hx, coefficientTensorLift_tmul]
      have hs := RingHom.congr_fun hlC s
      change lC (f s) = g (jS s) at hs
      rw [hs]
      change g (jS s) * g (jT t) = g (s ⊗ₜ[R] t)
      rw [← map_mul]
      congr 1
      change (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) = s ⊗ₜ[R] t
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · simp only [map_add, hx, hy]
  refine ⟨L, hLg, ?_⟩
  intro M hM
  have hMC : ((M.comp F).comp iC).comp f.toRingHom = g.comp jS := by
    apply RingHom.ext
    intro s
    have hs := RingHom.congr_fun hM (s ⊗ₜ[R] (1 : T))
    exact hs
  have heC : (M.comp F).comp iC = lC := hluniq _ hMC
  have heT (t : T) : M (F (iT t)) = g (jT t) := by
    have ht := RingHom.congr_fun hM ((1 : S) ⊗ₜ[R] t)
    change M (F (f 1 ⊗ₜ[R] t)) = g ((1 : S) ⊗ₜ[R] t) at ht
    rw [map_one] at ht
    exact ht
  apply huniq
  apply RingHom.ext
  intro x
  refine TensorProduct.inductionOn x (fun c t ↦ ?_) (fun x y hx hy ↦ ?_)
  · have ht : c ⊗ₜ[R] t = iC c * iT t := by
      change c ⊗ₜ[R] t = (c ⊗ₜ[R] (1 : T)) * ((1 : C) ⊗ₜ[R] t)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change M (F (c ⊗ₜ[R] t)) = coefficientTensorLift lC (g.comp jT) hi (c ⊗ₜ[R] t)
    rw [coefficientTensorLift_tmul, ht, map_mul, map_mul]
    have hc := RingHom.congr_fun heC c
    change M (F (iC c)) = lC c at hc
    rw [hc, heT]
    rfl
  · simp only [map_add, hx, hy]

/-- 任意perfectoid基底Rとperfectoid R-代数Tへの基底変更。
具体的候補E、Fのperfectoid化と標準mod p全単射性、底変換合成射の普遍性を得る。 -/
theorem exists_perfectoidizationTensorBaseChange (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    ∃ (E : Type u) (_ : CommRing E) (F : C ⊗[R] T →+* E),
      IsPerfectoidization p F ∧ Function.Bijective (modPMap p F) ∧
        IsPerfectoidization p (perfectoidizationTensorBaseChangeMap f F) := by
  obtain ⟨E, hE, F, hF, hbij⟩ := exists_perfectoidTensorPerfectoidization_modP p R C T
    hR hf.1 hT
  exact ⟨E, hE, F, hF, hbij,
    perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf F hF⟩

end SerrePositivity.BhattScholze
