module

public import SerrePositivity.BhattScholze.PerfectCoefficientTensor
public import SerrePositivity.CommutativeAlgebra.StrictPRecovery

/-! # B4-5：Witt係数テンソルから完備環への普遍射

既存の一般Witt持上げを用いる。完備テンソルを新しく定義せず、
完全係数環のテンソルのWitt環について、p完備試験環への普遍性を証明する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]
variable {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
variable [Algebra R A] [Algebra R B]
variable [CharP R p] [CharP A p] [CharP B p]
variable [PerfectRing R p] [PerfectRing A p] [PerfectRing B p]

private def wittMapResidue {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
    (f : WittVector p k →+* D) : k →+* ModP D p :=
  (WittVector.constantCoeff : WittVector p k →+* k).liftOfSurjective
    (WittVector.constantCoeff_surjective p)
    ⟨(Ideal.Quotient.mk (Ideal.span {(p : D)})).comp f, by
      rw [WittVector.ker_constantCoeff, Ideal.span_singleton_le_iff_mem]
      change Ideal.Quotient.mk (Ideal.span {(p : D)}) (f (p : WittVector p k)) = 0
      rw [map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩

private theorem wittMapResidue_coeff {k : Type u} [CommRing k] [CharP k p]
    [PerfectRing k p] (f : WittVector p k →+* D) (x : WittVector p k) :
    wittMapResidue p f (x.coeff 0) =
      Ideal.Quotient.mk (Ideal.span {(p : D)}) (f x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

private theorem wittMapResidue_teichmuller {k : Type u} [CommRing k] [CharP k p]
    [PerfectRing k p] (f : WittVector p k →+* D) (a : k) :
    wittMapResidue p f a =
      Ideal.Quotient.mk (Ideal.span {(p : D)}) (f (WittVector.teichmuller p a)) := by
  simpa using wittMapResidue_coeff p f (WittVector.teichmuller p a)

omit [CharP R p] [CharP A p] [CharP B p]
  [PerfectRing R p] [PerfectRing A p] [PerfectRing B p] in
/-- 両因子のWitt射は、基底のWitt環上で一致する。 -/
theorem wittCoefficientTensor_base_agreement :
    (WittVector.map (p := p)
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom).comp
        (WittVector.map (algebraMap R A)) =
    (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).comp
        (WittVector.map (algebraMap R B)) := by
  apply RingHom.ext
  intro x
  apply WittVector.ext
  intro n
  simp only [RingHom.comp_apply, WittVector.map_coeff, AlgHom.toRingHom_eq_coe]
  exact (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).commutes (x.coeff n) |>.trans
    ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).commutes (x.coeff n)).symm

variable [CharP (A ⊗[R] B) p] [PerfectRing (A ⊗[R] B) p]

omit [CharP R p] [CharP A p] [CharP B p]
  [PerfectRing R p] [PerfectRing A p] [PerfectRing B p] in
/-- 係数テンソルのWitt環からp Hausdorff環への射は両因子で決まる。 -/
theorem wittCoefficientTensorHom_ext [IsHausdorff (Ideal.span {(p : D)}) D]
    (f g : WittVector p (A ⊗[R] B) →+* D)
    (hA : f.comp (WittVector.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) =
      g.comp (WittVector.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom))
    (hB : f.comp (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
      g.comp (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)) : f = g := by
  have hres : wittMapResidue p f = wittMapResidue p g := by
    apply RingHom.ext
    intro x
    refine TensorProduct.inductionOn x (fun a b ↦ ?_) (fun x y hx hy ↦ ?_)
    · let iA := (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
      let iB := (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
      have ht : a ⊗ₜ[R] b = iA a * iB b := by
        change a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have ha : wittMapResidue p f (iA a) = wittMapResidue p g (iA a) := by
        rw [wittMapResidue_teichmuller, wittMapResidue_teichmuller]
        have he := RingHom.congr_fun hA (WittVector.teichmuller p a)
        simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
          congrArg (Ideal.Quotient.mk (Ideal.span {(p : D)})) he
      have hb : wittMapResidue p f (iB b) = wittMapResidue p g (iB b) := by
        rw [wittMapResidue_teichmuller, wittMapResidue_teichmuller]
        have he := RingHom.congr_fun hB (WittVector.teichmuller p b)
        simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
          congrArg (Ideal.Quotient.mk (Ideal.span {(p : D)})) he
      rw [ht, map_mul, map_mul, ha, hb]
    · simp only [map_add, hx, hy]
  apply wittLift_unique
  apply RingHom.ext
  intro x
  change Ideal.Quotient.mk _ (f x) = Ideal.Quotient.mk _ (g x)
  rw [← wittMapResidue_coeff p f x, ← wittMapResidue_coeff p g x, hres]

omit [CharP R p] [PerfectRing R p] in
/-- 完全係数テンソルのWitt環は、任意のp完備環への両立するWitt射を一意に延長する。
終域のp正則性・非零性は要求しない。 -/
theorem existsUnique_wittCoefficientTensorLift
    [IsAdicComplete (Ideal.span {(p : D)}) D]
    (f : WittVector p A →+* D) (g : WittVector p B →+* D)
    (h : f.comp (WittVector.map (algebraMap R A)) =
      g.comp (WittVector.map (algebraMap R B))) :
    ∃! L : WittVector p (A ⊗[R] B) →+* D,
      L.comp (WittVector.map
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) = f ∧
      L.comp (WittVector.map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) = g := by
  let sA := wittMapResidue p f
  let sB := wittMapResidue p g
  have hs : ∀ r : R, sA (algebraMap R A r) = sB (algebraMap R B r) := by
    intro r
    rw [wittMapResidue_teichmuller, wittMapResidue_teichmuller]
    have he := RingHom.congr_fun h (WittVector.teichmuller p r)
    simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
      congrArg (Ideal.Quotient.mk (Ideal.span {(p : D)})) he
  let s := coefficientTensorLift sA sB hs
  obtain ⟨L, hL, _⟩ := existsUnique_wittResidueLift_of_complete p D (A ⊗[R] B) s
  have hLA : L.comp (WittVector.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) = f := by
    apply wittLift_unique
    apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun hL (WittVector.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom x)
    change Ideal.Quotient.mk _ (L (WittVector.map _ x)) = _ at hx ⊢
    rw [hx]
    change s (x.coeff 0 ⊗ₜ[R] (1 : B)) = _
    rw [coefficientTensorLift_tmul, map_one, mul_one]
    exact wittMapResidue_coeff p f x
  have hLB : L.comp (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) = g := by
    apply wittLift_unique
    apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun hL (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom x)
    change Ideal.Quotient.mk _ (L (WittVector.map _ x)) = _ at hx ⊢
    rw [hx]
    change s ((1 : A) ⊗ₜ[R] x.coeff 0) = _
    rw [coefficientTensorLift_tmul, map_one, one_mul]
    exact wittMapResidue_coeff p g x
  refine ⟨L, ⟨hLA, hLB⟩, ?_⟩
  intro M hM
  exact wittCoefficientTensorHom_ext p M L (hM.1.trans hLA.symm) (hM.2.trans hLB.symm)

omit [CharP (A ⊗[R] B) p] [PerfectRing (A ⊗[R] B) p] in
/-- 完全係数環の両立するWitt射の延長。係数テンソルが零環の場合も含む。 -/
theorem existsUnique_wittCoefficientTensorLift_of_perfect
    [IsAdicComplete (Ideal.span {(p : D)}) D]
    (f : WittVector p A →+* D) (g : WittVector p B →+* D)
    (h : f.comp (WittVector.map (algebraMap R A)) =
      g.comp (WittVector.map (algebraMap R B))) :
    ∃! L : WittVector p (A ⊗[R] B) →+* D,
      L.comp (WittVector.map
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) = f ∧
      L.comp (WittVector.map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) = g := by
  let K := A ⊗[R] B
  rcases subsingleton_or_nontrivial K with hK | hK
  · let := hK
    let sA := wittMapResidue p f
    let sB := wittMapResidue p g
    have hs : ∀ r : R, sA (algebraMap R A r) = sB (algebraMap R B r) := by
      intro r
      rw [wittMapResidue_teichmuller, wittMapResidue_teichmuller]
      have he := RingHom.congr_fun h (WittVector.teichmuller p r)
      simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
        congrArg (Ideal.Quotient.mk (Ideal.span {(p : D)})) he
    let s := coefficientTensorLift sA sB hs
    have h01 : (1 : ModP D p) = 0 := by
      rw [← s.map_one, Subsingleton.elim (1 : K) 0, s.map_zero]
    have hu : IsUnit (p : D) := by
      apply Ideal.span_singleton_eq_top.mp
      apply (Ideal.eq_top_iff_one _).mpr
      exact Ideal.Quotient.eq_zero_iff_mem.mp h01
    let := subsingleton_of_isUnit_natCast_of_isHausdorff p D hu
    let L : WittVector p K →+* D :=
      { toFun := fun _ ↦ 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
    refine ⟨L, ⟨?_, ?_⟩, ?_⟩
    · ext x
      exact Subsingleton.elim _ _
    · ext x
      exact Subsingleton.elim _ _
    · intro M _
      ext x
      exact Subsingleton.elim _ _
  · let := hK
    have hp : (p : K) = 0 := by
      rw [← map_natCast (algebraMap R K), CharP.cast_eq_zero, map_zero]
    let : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    let : PerfectRing K p := perfectCoefficientTensor_perfectRing p R A B
    exact existsUnique_wittCoefficientTensorLift p f g h

end SerrePositivity.BhattScholze
