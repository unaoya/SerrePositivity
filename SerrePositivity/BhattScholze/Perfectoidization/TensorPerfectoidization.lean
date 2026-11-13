module

public import SerrePositivity.BhattScholze.Perfectoidization.WittPushout
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Completion
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid

/-!
# perfectoid 環の通常テンソル積の perfectoid 化と底変換

## 概要
Witt 商表示を持つ環のテンソル積の perfectoid 化、任意の perfectoid 環の通常テンソル積の perfectoid 化、普遍 perfectoid 化の通常テンソルによる底変換。

## 方針
Witt 余積の普遍性を IsPerfectoidization へ移す。

## 規約
—

## 使われ方
perfectoid 環の完備テンソル積、BS 著者版 Theorem 7.4 の底変換。
-/

universe u

/-! ## Witt商表示を持つ環のテンソルからのperfectoid化

共通のWitt基底写像に沿う商表示と図式を明示して入力する。
標準Fontaine商表示をこの入口へ供給する工程とmod p比較は別に残る。
-/

@[expose] public noncomputable section WittPresentedPerfectoidTensor

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

end WittPresentedPerfectoidTensor

/-! ## 全p完備試験環への普遍性からの標準mod p比較

pが零の試験環は自動的にp完備であることを使う。
通常テンソルの標準射のmod pが同型であることを証明する。
導来テンソルの比較には置換しない。
-/

@[expose] public noncomputable section WittPresentedPerfectoidTensorModP

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

end WittPresentedPerfectoidTensorModP

/-! ## 任意perfectoid環の通常テンソルのperfectoid化

標準Fontaine表示と自然性を実際のperfectoid入力から供給する。
基底・両因子・係数テンソルの零環の場合も含む。mod p比較は別工程。
-/

@[expose] public noncomputable section PerfectoidTensorPerfectoidization

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct

/-- perfectoid環R上の任意のperfectoid環S,Tの通常テンソルにはperfectoid化が存在する。
有限性・p正則性・非零性を要求しない。 -/
theorem exists_perfectoidTensorPerfectoidization_modP (p : ℕ) [Fact p.Prime]
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    ∃ (E : Type u) (_ : CommRing E) (F : S ⊗[R] T →+* E),
      IsPerfectoidization p F ∧ Function.Bijective (modPMap p F) := by
  rcases subsingleton_or_nontrivial (S ⊗[R] T) with hzero | hn
  · let := hzero
    refine ⟨S ⊗[R] T, inferInstance, RingHom.id _, ⟨Or.inl hzero, ?_⟩, ?_⟩
    · intro D _ _ g
      refine ⟨g, RingHom.comp_id g, ?_⟩
      intro L hL
      simpa only [RingHom.comp_id] using hL
    · exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
        fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩
  · let := hn
    let : Nontrivial R := (algebraMap R (S ⊗[R] T)).domain_nontrivial
    let : Nontrivial S :=
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom.domain_nontrivial
    let : Nontrivial T :=
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom.domain_nontrivial
    rcases hR with hzero | ⟨hpR, hcR, ⟨π, u, hpEq⟩, hFR, hkerR⟩
    · let := hzero
      exact (zero_ne_one (Subsingleton.elim (0 : R) 1)).elim
    rcases hS with hzero | ⟨hpS, hcS, _, hFS, hkerS⟩
    · let := hzero
      exact (zero_ne_one (Subsingleton.elim (0 : S) 1)).elim
    rcases hT with hzero | ⟨hpT, hcT, _, hFT, hkerT⟩
    · let := hzero
      exact (zero_ne_one (Subsingleton.elim (0 : T) 1)).elim
    let : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
    let : Fact (¬ IsUnit (p : S)) := ⟨hpS⟩
    let : Fact (¬ IsUnit (p : T)) := ⟨hpT⟩
    let := hcR
    let := hcS
    let := hcT
    obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator R p
      hFR hkerR π u hpEq
    have hzero : WittVector.fontaineTheta R p d = 0 := by
      apply RingHom.mem_ker.mp
      rw [hk]
      exact Ideal.mem_span_singleton_self _
    let kR := PreTilt R p
    let kS := PreTilt S p
    let kT := PreTilt T p
    let : Algebra kR kS := (Perfection.map p (modPMap p (algebraMap R S))).toAlgebra
    let : Algebra kR kT := (Perfection.map p (modPMap p (algebraMap R T))).toAlgebra
    let eS := fontaineBaseWittQuotientEquiv p (algebraMap R S) d hd hzero hFS hkerS
    let eT := fontaineBaseWittQuotientEquiv p (algebraMap R T) d hd hzero hFT hkerT
    have heS : (eS.toRingHom.comp (Ideal.Quotient.mk _)).comp
        (WittVector.map (algebraMap kR kS)) =
        (algebraMap R S).comp (WittVector.fontaineTheta R p) := by
      rw [fontaineBaseWittQuotientEquiv_comp_mk]
      exact fontaineTheta_natural p (algebraMap R S)
    have heT : (eT.toRingHom.comp (Ideal.Quotient.mk _)).comp
        (WittVector.map (algebraMap kR kT)) =
        (algebraMap R T).comp (WittVector.fontaineTheta R p) := by
      rw [fontaineBaseWittQuotientEquiv_comp_mk]
      exact fontaineTheta_natural p (algebraMap R T)
    obtain ⟨F, _, _, hF, hbij⟩ := exists_wittPresentedTensorPerfectoidization_modP p kR kS kT d hd
      (WittVector.fontaineTheta R p) (fun x ↦ surjective_fontaineTheta hFR x) eS eT heS heT
    exact ⟨WittCoefficientPushout p kR kS kT d, inferInstance, F, hF, hbij⟩

/-- 任意perfectoid環の通常テンソルのperfectoid化の存在。 -/
theorem exists_perfectoidTensorPerfectoidization (p : ℕ) [Fact p.Prime]
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    ∃ (E : Type u) (_ : CommRing E) (F : S ⊗[R] T →+* E), IsPerfectoidization p F := by
  obtain ⟨E, hE, F, hF, _⟩ := exists_perfectoidTensorPerfectoidization_modP p R S T hR hS hT
  exact ⟨E, hE, F, hF⟩

end SerrePositivity.BhattScholze

end PerfectoidTensorPerfectoidization

/-! ## 普遍perfectoid化の通常テンソルによる基底変更

共通基底の代数写像を用い、具体的な合成射の普遍性を証明する。
底変換した射の全射性やmod p比較はこの定理の結論に含めない。
-/

@[expose] public noncomputable section PerfectoidizationBaseChange

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

end PerfectoidizationBaseChange
