module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismQuotientPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaPDQuotientEquiv
public import SerrePositivity.CommutativeAlgebra.AdicCompletionAlgebraUniversal
/-! # Distinguished 商の通常 p 進完備化の perfectoid 性

BS Thm 3.10（著者版 p.32）と Thm 7.14（p.61）の極限段に用いる補助命題。
完全 δ 環の distinguished 商を通常に p 進完備化したものを、既存の実 PD 完備化の
完全 prism の商と、二つの普遍性から同一視する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.BhattScholze.Andre.Transfinite
open SerrePositivity SerrePositivity.BhattScholze SerrePositivity.DerivedCompletion
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- ## 概要
完全 δ 環 A の distinguished 元 d を核の生成元とする全射 A → T に対し、
T の通常の p 進完備化は perfectoid。BS Thm 3.10（著者版 p.32）、Thm 7.14（p.61）の補助命題。

## 方針
既存の実 PD 完備化から得る完全 prism の商 Q を使う。T の通常完備化 C と Q の間に、
通常完備化と実 PD 完備化の普遍性から互いに逆な環準同型を構成する。
Q の perfectoid 性を、得られた環同型で C へ移す。

## 規約
T の p 正則性・被約性・有界ねじれ・完備性は仮定しない。
通常完備化を実導来完備化と無条件に同一視せず、実際の二つの環普遍性を照合する。

## 使われ方
perfectoid 塔の未完備余極限を、完全 δ 環の distinguished 商として表示した後、
その p 進完備化の perfectoid 性を得る。
-/
theorem isIntegralPerfectoid_adicCompletion_of_distinguished_kernel {p : ℕ} [Fact p.Prime]
    {A T : Type u} [CommRing A] [CommRing T]
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d)
    (q₀ : A →+* T) (hq₀ : Function.Surjective q₀)
    (hk₀ : RingHom.ker q₀ = Ideal.span {d}) :
    IsIntegralPerfectoid (AdicCompletion (Ideal.span {(p : T)}) T) p := by
  let I : Ideal T := Ideal.span {(p : T)}
  let C := AdicCompletion I T
  let k : T →+* C := algebraMap T C
  have hI : I.FG := Submodule.fg_span (Set.toFinite _)
  let : IsAdicComplete I C := AdicCompletion.isAdicComplete hI
  have hmap : I.map k = Ideal.span {(p : C)} := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : C ↦ Ideal.span {z}) (map_natCast k p)
  let : IsAdicComplete (Ideal.span {(p : C)}) C := by
    rw [← hmap]
    exact (IsAdicComplete.map_algebraMap_iff (I := I) (S := C) (M := C)).mpr inferInstance
  let := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  let Q := H ⧸ Ideal.span {j d}
  let q : H →+* Q := Ideal.Quotient.mk _
  let : IsAdicComplete (Ideal.span {(p : Q)}) Q :=
    perfectDeltaPDPrism_quotient_isAdicComplete D hD d hd
  have hpQ := isModuleComplete_of_isAdicComplete Q (p : Q) (ModuleCat.of Q Q)
  have hqd : q (j d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hz (B : Type u) [CommRing B] : IsModuleComplete B (0 : B) (ModuleCat.of B B) :=
    isModuleComplete_of_pow_smul_zero B 0 _ 1 (by simp)
  have hdQ : IsModuleComplete Q ((q.comp j) d) (ModuleCat.of Q Q) := hqd ▸ hz Q
  let f : A →+* C := k.comp q₀
  have hq₀d : q₀ d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk₀]
    exact Ideal.mem_span_singleton_self _
  have hfd : f d = 0 := by
    change k (q₀ d) = 0
    rw [hq₀d, map_zero]
  have hpC := isModuleComplete_of_isAdicComplete C (p : C) (ModuleCat.of C C)
  have hdC : IsModuleComplete C (f d) (ModuleCat.of C C) := hfd ▸ hz C
  obtain ⟨g, hg, _⟩ := existsUnique_pdCompletionRingHom A p d C f hpC hdC
  have hgd : g (j d) = 0 := (RingHom.congr_fun hg d).trans hfd
  let b : Q →+* C := Ideal.Quotient.lift _ g (by
    change Ideal.span {j d} ≤ RingHom.ker g
    exact (Ideal.span_singleton_le_iff_mem _).mpr hgd)
  have hb : b.comp q = g := Ideal.Quotient.lift_comp_mk _ _ _
  have hfactor : RingHom.ker q₀ ≤ RingHom.ker (q.comp j) := by
    rw [hk₀]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hqd
  let t : T →+* Q := q₀.liftOfSurjective hq₀ ⟨q.comp j, hfactor⟩
  have ht : t.comp q₀ = q.comp j := q₀.liftOfSurjective_comp hq₀ _
  let := t.toAlgebra
  have hmapT : I.map (algebraMap T Q) = Ideal.span {(p : Q)} := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : Q ↦ Ideal.span {z}) (map_natCast (algebraMap T Q) p)
  let : IsAdicComplete I Q := by
    apply (IsAdicComplete.map_algebraMap_iff (I := I) (S := Q) (M := Q)).mp
    rw [hmapT]
    infer_instance
  let i := adicCompletionToCompleteAlgebra T I hI Q
  have hi : i.toRingHom.comp k = t := by
    ext r
    exact i.commutes r
  let ba : Q →ₐ[T] C :=
    { b with
      commutes' := by
        intro r
        obtain ⟨a, rfl⟩ := hq₀ r
        change b (t (q₀ a)) = k (q₀ a)
        have hta := RingHom.congr_fun ht a
        change t (q₀ a) = q (j a) at hta
        rw [hta]
        have hba := RingHom.congr_fun hb (j a)
        change b (q (j a)) = g (j a) at hba
        rw [hba]
        exact RingHom.congr_fun hg a }
  have hbi : b.comp i.toRingHom = RingHom.id C := by
    exact congrArg AlgHom.toRingHom (adicCompletion_algHom_ext T I hI C
      (ba.comp i) (AlgHom.id T C))
  have hib : i.toRingHom.comp b = RingHom.id Q := by
    apply Ideal.Quotient.ringHom_ext
    change (i.toRingHom.comp b).comp q = (RingHom.id Q).comp q
    rw [RingHom.comp_assoc, hb, RingHom.id_comp]
    apply pdCompletionRingHom_ext A p d Q (q.comp j) hpQ hdQ
    · ext a
      have hga := RingHom.congr_fun hg a
      change g (j a) = k (q₀ a) at hga
      change i (g (j a)) = q (j a)
      rw [hga]
      have hia := RingHom.congr_fun hi (q₀ a)
      change i (k (q₀ a)) = t (q₀ a) at hia
      rw [hia]
      exact RingHom.congr_fun ht a
    · rfl
  let e : Q ≃+* C :=
    { b with invFun := i, left_inv := RingHom.congr_fun hib, right_inv := RingHom.congr_fun hbi }
  have hQ : IsIntegralPerfectoid Q p :=
    OrientedPrism.quotient_isIntegralPerfectoid (perfectDeltaPDPrism D hD d hd)
      (perfectDeltaPDPrism_isPerfect D hD d hd)
  exact isIntegralPerfectoid_of_ringEquiv p e hQ

end SerrePositivity.BhattScholze.Andre.Transfinite
