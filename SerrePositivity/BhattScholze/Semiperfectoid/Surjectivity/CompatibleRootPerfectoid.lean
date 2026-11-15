module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.CompatibleRoot

/-!
# 互換 p 冪根の商の完備化は perfectoid

## 概要
完全 prism 商への射が延長する完備な全射候補と導来 PD 完備化商の比較、単一根・根族の場合の比較、互換根商の完備化の perfectoid 性。
BS 著者版 Theorem 7.4 の根付き拡大による証明に使う、互換 p 冪根の商の perfectoid 性を示す。

## 方針
完全 prism の Witt 表示と PD 完備化商の比較から perfectoid 性を移す。

## 規約
—

## 使われ方
CLMST の perfectoid イデアル（CommutativeAlgebra/PerfectoidIdealCompatibleRoots・PerfectoidIdealCover）。
-/

universe u

/-! ## semiperfectoid 環の商比較の共通部分

完全prism商への射が延長する完備な全射候補と、実PD完備化商を比較する。
単項と任意根族で同じ比較証明を共有するためのBS専用補題。
-/

@[expose] public noncomputable section PerfectDeltaPDQuotientComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R A B C : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing C]

/-- 完備な全射候補のperfectoid試験環への延長性から、実PD商との比較同型を得る。 -/
theorem Semiperfectoid.exists_perfectDeltaPDQuotientEquiv_of_perfectoidExtension
    [IsAdicComplete (Ideal.span {(p : C)}) C]
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p B) (hD : D.IsPerfect) (d : A)
    (θ : A →+* R) (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {d})
    (w : A →+* B) (hw : Function.Surjective w) (hd : D.IsDistinguished (w d))
    (I : Ideal R) (hI : I ≤ (RingHom.ker w).map θ)
    (qR : R →+* C) (hqR : Function.Surjective qR)
    (hExtend : ∀ (T : Type u) [CommRing T], _root_.SerrePositivity.IsIntegralPerfectoid T p →
      ∀ i : R →+* T, I ≤ RingHom.ker i → ∃ c : C →+* T, c.comp qR = i)
    (β : B →+* C) (hβ : β.comp w = qR.comp θ) :
    letI := pdCompletionCommRing B p (w d)
    ∃ e : C ≃+* PDCompletionH0 B p (w d) ⧸ Ideal.span {pdCompletionUnit B p (w d) (w d)},
      e.toRingHom.comp qR =
        θ.liftOfSurjective hθ ⟨(Ideal.Quotient.mk _).comp
          ((pdCompletionUnit B p (w d)).comp w), by
            rw [hker, Ideal.span_singleton_le_iff_mem]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩ := by
  let := pdCompletionCommRing B p (w d)
  let H := PDCompletionH0 B p (w d)
  let j := pdCompletionUnit B p (w d)
  let U := H ⧸ Ideal.span {j (w d)}
  let qU := Ideal.Quotient.mk (Ideal.span {j (w d)})
  let := _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism_quotient_isAdicComplete D hD (w d) hd
  let i : R →+* U := θ.liftOfSurjective hθ ⟨qU.comp (j.comp w), by
    rw [hker, Ideal.span_singleton_le_iff_mem]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩
  have hiθ : i.comp θ = qU.comp (j.comp w) := θ.liftOfSurjective_comp hθ _
  have hiI : I ≤ RingHom.ker i := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := Ideal.mem_image_of_mem_map_of_surjective θ hθ (hI hr)
    change i r = 0
    rw [← hxr]
    have hh : i (θ x) = qU (j (w x)) := RingHom.congr_fun hiθ x
    rw [hh, show w x = 0 from hx, map_zero, map_zero]
  have hU : _root_.SerrePositivity.IsIntegralPerfectoid U p :=
    (_root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism D hD (w d) hd).quotient_isIntegralPerfectoid
      (_root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism_isPerfect D hD (w d) hd)
  obtain ⟨c, hcR⟩ := hExtend U hU i hiI
  have hθd : θ d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.mem_span_singleton_self _
  have hβd : β (w d) = 0 := by
    have hh : β (w d) = qR (θ d) := RingHom.congr_fun hβ d
    rw [hh, hθd, map_zero]
  have hz (T : Type u) [CommRing T] : IsModuleComplete T (0 : T) (ModuleCat.of T T) :=
    isModuleComplete_of_pow_smul_zero T 0 _ 1 (by simp)
  have hpC := isModuleComplete_of_isAdicComplete C (p : C) (ModuleCat.of C C)
  have hdC : IsModuleComplete C (β (w d)) (ModuleCat.of C C) := hβd ▸ hz C
  obtain ⟨b, hb, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_pdCompletionRingHom B p (w d) C β hpC hdC
  let b0 : U →+* C := Ideal.Quotient.lift _ b (by
    change Ideal.span {j (w d)} ≤ RingHom.ker b
    rw [Ideal.span_singleton_le_iff_mem]
    have hh : b (j (w d)) = β (w d) := RingHom.congr_fun hb (w d)
    exact hh.trans hβd)
  have hbq : b0.comp qU = b := rfl
  have hbi : b0.comp i = qR := by
    apply (RingHom.cancel_right hθ).mp
    rw [RingHom.comp_assoc, hiθ, ← RingHom.comp_assoc, hbq,
      ← RingHom.comp_assoc, hb, hβ]
  have hbc : b0.comp c = RingHom.id C := by
    apply (RingHom.cancel_right hqR).mp
    rw [RingHom.comp_assoc, hcR, hbi, RingHom.id_comp]
  have hcb : c.comp b0 = RingHom.id U := by
    apply Ideal.Quotient.ringHom_ext
    have hcbβ : c.comp β = qU.comp j := by
      apply (RingHom.cancel_right hw).mp
      rw [RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hcR, hiθ,
        RingHom.comp_assoc]
    have hpU := isModuleComplete_of_isAdicComplete U (p : U) (ModuleCat.of U U)
    have hqd : (qU.comp j) (w d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    have hdU : IsModuleComplete U ((qU.comp j) (w d)) (ModuleCat.of U U) := hqd ▸ hz U
    have he : c.comp b = qU := by
      apply _root_.SerrePositivity.BhattScholze.pdCompletionRingHom_ext B p (w d) U (qU.comp j) hpU hdU
      · rw [RingHom.comp_assoc, hb, hcbβ]
      · rfl
    change (c.comp b0).comp qU = (RingHom.id U).comp qU
    rw [RingHom.comp_assoc, hbq, he, RingHom.id_comp]
  refine ⟨{ c with
    invFun := b0
    left_inv := RingHom.congr_fun hbc
    right_inv := RingHom.congr_fun hcb }, hcR⟩

end SerrePositivity.BhattScholze

end PerfectDeltaPDQuotientComparison

/-! ## 一元添字の根族と既存の単一根商・完備化の比較

元の単一根の台環と標準射を変更せず、イデアルの一致から比較する。
根の関係式、素数性、完備性、perfectoid性はこの比較自体には要求しない。
-/

@[expose] public noncomputable section CompatibleRootSingletonComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R : Type u} [CommRing R]

/-- 一元添字族の初期イデアルは、元の単一根の初期主イデアル。 -/
theorem Semiperfectoid.compatibleRootFamilyZeroIdeal_singleton (ρ : ℕ → R) :
    _root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal (fun _ : PUnit.{u+1} ↦ ρ) = Ideal.span {ρ 0} := by
  change Ideal.span (Set.range (fun _ : PUnit.{u+1} ↦ ρ 0)) = Ideal.span {ρ 0}
  rw [Set.range_const]

/-- 一元添字族の全根イデアルは、元の単一根イデアル。 -/
theorem Semiperfectoid.compatibleRootFamilyIdeal_singleton (ρ : ℕ → R) :
    _root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ) = _root_.SerrePositivity.BhattScholze.compatibleRootIdeal ρ := by
  change Ideal.span (Set.range (fun x : PUnit.{u+1} × ℕ ↦ ρ x.2)) =
    Ideal.span (Set.range ρ)
  congr 1
  ext x
  constructor
  · rintro ⟨⟨_, n⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(PUnit.unit, n), rfl⟩

/-- 初期イデアルの一致による標準商比較。 -/
def Semiperfectoid.compatibleRootSingletonZeroQuotientEquiv (ρ : ℕ → R) :
    R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal (fun _ : PUnit.{u+1} ↦ ρ) ≃+* R ⧸ Ideal.span {ρ 0} :=
  Ideal.quotEquivOfEq (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyZeroIdeal_singleton ρ)

@[simp] theorem Semiperfectoid.compatibleRootSingletonZeroQuotientEquiv_mk (ρ : ℕ → R) (r : R) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonZeroQuotientEquiv ρ (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl

/-- 全根イデアルの一致による標準商比較。 -/
def Semiperfectoid.compatibleRootSingletonQuotientEquiv (ρ : ℕ → R) :
    R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ) ≃+* R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootIdeal ρ :=
  Ideal.quotEquivOfEq (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyIdeal_singleton ρ)

@[simp] theorem Semiperfectoid.compatibleRootSingletonQuotientEquiv_mk (ρ : ℕ → R) (r : R) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonQuotientEquiv ρ (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl

/-- 二つの商比較は、初期商から全根商への元の標準射と可換。 -/
theorem Semiperfectoid.compatibleRootSingletonQuotientEquiv_comp_quotientMap (ρ : ℕ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonQuotientEquiv ρ).toRingHom.comp
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyQuotientMap (fun _ : PUnit.{u+1} ↦ ρ)) =
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootQuotientMap ρ).comp
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonZeroQuotientEquiv ρ).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  rfl

/-- 同じ全根イデアルの一致だけを使った、既存p完備化の比較。 -/
def Semiperfectoid.compatibleRootSingletonCompletionEquiv (p : ℕ) (ρ : ℕ → R) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootFamilyCompletion p (fun _ : PUnit.{u+1} ↦ ρ) ≃+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootCompletion p ρ :=
  RingEquiv.cast (R := fun I : Ideal R ↦ AdicCompletion (Ideal.span {(p : R ⧸ I)}) (R ⧸ I))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyIdeal_singleton ρ)

private theorem Semiperfectoid.completionCast_algebraMap (p : ℕ) {I J : Ideal R} (h : I = J) (x : R ⧸ I) :
    RingEquiv.cast (R := fun K : Ideal R ↦ AdicCompletion (Ideal.span {(p : R ⧸ K)}) (R ⧸ K)) h
        (algebraMap (R ⧸ I) _ x) =
      algebraMap (R ⧸ J) _ (Ideal.quotEquivOfEq h x) := by
  subst J
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- 完備化比較は、全根商からの元の標準単位を保つ。 -/
@[simp] theorem Semiperfectoid.compatibleRootSingletonCompletionEquiv_algebraMap (p : ℕ) (ρ : ℕ → R)
    (x : R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ)) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonCompletionEquiv p ρ (algebraMap _ _ x) =
      algebraMap _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootCompletion p ρ) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonQuotientEquiv ρ x) :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.completionCast_algebraMap p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyIdeal_singleton ρ) x

/-- 完備化比較は、初期商からの既存compatibleRootCompletionMapを保つ。 -/
theorem Semiperfectoid.compatibleRootSingletonCompletionEquiv_comp_completionMap (p : ℕ) (ρ : ℕ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonCompletionEquiv p ρ).toRingHom.comp
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap p (fun _ : PUnit.{u+1} ↦ ρ)) =
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap p ρ).comp
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonZeroQuotientEquiv ρ).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  change _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonCompletionEquiv p ρ
      (algebraMap (R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ)) _
        (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ)) r)) =
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap p ρ
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonZeroQuotientEquiv ρ
        (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal (fun _ : PUnit.{u+1} ↦ ρ)) r))
  rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonCompletionEquiv_algebraMap,
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonQuotientEquiv_mk, _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonZeroQuotientEquiv_mk]
  rfl

end SerrePositivity.BhattScholze

end CompatibleRootSingletonComparison

/-! ## 古典的根イデアル商の完備化と実PD完備化商の比較

具体的な標準射の図式と全射性から比較同型を証明する。
古典的完備化と実導来完備化を無条件に同一視しない。
-/

@[expose] public noncomputable section CompatibleRootPDComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

omit [Fact p.Prime] in
/-- 根イデアル商の古典的p完備化は、自身のp作用についてp完備。 -/
theorem Semiperfectoid.compatibleRootCompletion_isAdicComplete (ρ : ℕ → R) :
    IsAdicComplete (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootCompletion p ρ)})
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootCompletion p ρ) := by
  let Q := R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootIdeal ρ
  let I : Ideal Q := Ideal.span {(p : Q)}
  have h := AdicCompletion.isAdicComplete (M := Q) (Submodule.fg_span_singleton (p : Q))
  have hm : I.map (algebraMap Q (AdicCompletion I Q)) =
      Ideal.span {(p : AdicCompletion I Q)} :=
    _root_.SerrePositivity.pIdeal_map Q (AdicCompletion I Q) p (algebraMap Q (AdicCompletion I Q))
  rw [← hm]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr h

/-- 根を消すWitt型商と実PD完備化の具体的図式から、古典的候補との比較同型を得る。 -/
theorem Semiperfectoid.exists_compatibleRootCompletionPDQuotientEquiv
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p B) (hD : D.IsPerfect) (d : A)
    (θ : A →+* R) (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {d})
    (w : A →+* B) (hw : Function.Surjective w) (hd : D.IsDistinguished (w d))
    (β : B →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootCompletion p ρ)
    (hβ : β.comp w = ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap p ρ).comp
      (Ideal.Quotient.mk (Ideal.span {ρ 0}))).comp θ)
    (a : A) (ha : θ a = ρ 0) (hwa : w a = 0) :
    letI := pdCompletionCommRing B p (w d)
    ∃ e : _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootCompletion p ρ ≃+*
        PDCompletionH0 B p (w d) ⧸ Ideal.span {pdCompletionUnit B p (w d) (w d)},
      e.toRingHom.comp ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap p ρ).comp
        (Ideal.Quotient.mk (Ideal.span {ρ 0}))) =
        θ.liftOfSurjective hθ ⟨(Ideal.Quotient.mk _).comp
          ((pdCompletionUnit B p (w d)).comp w), by
            rw [hker, Ideal.span_singleton_le_iff_mem]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩ := by
  let := pdCompletionCommRing B p (w d)
  let := hR.isAdicComplete R p
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletion_isAdicComplete (p := p) ρ
  let qR := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap p ρ).comp (Ideal.Quotient.mk (Ideal.span {ρ 0}))
  have hqR : Function.Surjective qR :=
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap_surjective (p := p) ρ).comp Ideal.Quotient.mk_surjective
  have hI : Ideal.span {ρ 0} ≤ (RingHom.ker w).map θ := by
    rw [Ideal.span_singleton_le_iff_mem, ← ha]
    exact Ideal.mem_map_of_mem θ (show a ∈ RingHom.ker w from hwa)
  have hExtend : ∀ (T : Type u) [CommRing T], _root_.SerrePositivity.IsIntegralPerfectoid T p →
      ∀ i : R →+* T, Ideal.span {ρ 0} ≤ RingHom.ker i →
        ∃ c : _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootCompletion p ρ →+* T, c.comp qR = i := by
    intro T _ hT i hi
    let i0 := Ideal.Quotient.lift (Ideal.span {ρ 0}) i hi
    obtain ⟨c, hc, _⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_compatibleRootCompletionLift_to_perfectoid ρ hρ hT i0
    refine ⟨c, ?_⟩
    change c.comp ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap p ρ).comp
      (Ideal.Quotient.mk (Ideal.span {ρ 0}))) = i
    rw [← RingHom.comp_assoc, hc]
    rfl
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectDeltaPDQuotientEquiv_of_perfectoidExtension D hD d θ hθ hker
    w hw hd (Ideal.span {ρ 0}) hI qR hqR hExtend β hβ

end SerrePositivity.BhattScholze

end CompatibleRootPDComparison

/-! ## 任意根族の完備化と実PD商の比較 -/

@[expose] public noncomputable section CompatibleRootFamilyPDComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable {σ : Type u}

omit [Fact p.Prime] in
/-- 任意根族商の完備化は、自身のp作用についてp完備。 -/
theorem Semiperfectoid.compatibleRootFamilyCompletion_isAdicComplete (ρ : σ → ℕ → R) :
    IsAdicComplete (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootFamilyCompletion p ρ)})
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootFamilyCompletion p ρ) := by
  let Q := R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal ρ
  let I : Ideal Q := Ideal.span {(p : Q)}
  have h := AdicCompletion.isAdicComplete (M := Q) (Submodule.fg_span_singleton (p : Q))
  have hm : I.map (algebraMap Q (AdicCompletion I Q)) =
      Ideal.span {(p : AdicCompletion I Q)} :=
    _root_.SerrePositivity.pIdeal_map Q (AdicCompletion I Q) p (algebraMap Q (AdicCompletion I Q))
  rw [← hm]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr h

/-- 全根族を消す具体的なWitt型商から、古典的候補と実PD商の比較同型を得る。 -/
theorem Semiperfectoid.exists_compatibleRootFamilyCompletionPDQuotientEquiv
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p)
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p B) (hD : D.IsPerfect) (d : A)
    (θ : A →+* R) (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {d})
    (w : A →+* B) (hw : Function.Surjective w) (hd : D.IsDistinguished (w d))
    (β : B →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootFamilyCompletion p ρ)
    (hβ : β.comp w = ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap p ρ).comp
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ))).comp θ)
    (a : σ → A) (ha : ∀ s, θ (a s) = ρ s 0) (hwa : ∀ s, w (a s) = 0) :
    letI := pdCompletionCommRing B p (w d)
    ∃ e : _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootFamilyCompletion p ρ ≃+*
        PDCompletionH0 B p (w d) ⧸ Ideal.span {pdCompletionUnit B p (w d) (w d)},
      e.toRingHom.comp ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap p ρ).comp
        (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ))) =
        θ.liftOfSurjective hθ ⟨(Ideal.Quotient.mk _).comp
          ((pdCompletionUnit B p (w d)).comp w), by
            rw [hker, Ideal.span_singleton_le_iff_mem]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩ := by
  let := pdCompletionCommRing B p (w d)
  let := hR.isAdicComplete R p
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletion_isAdicComplete (p := p) ρ
  let qR := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap p ρ).comp
    (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ))
  have hqR : Function.Surjective qR :=
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap_surjective (p := p) ρ).comp Ideal.Quotient.mk_surjective
  have hI : _root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ ≤ (RingHom.ker w).map θ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change ρ s 0 ∈ (RingHom.ker w).map θ
    rw [← ha s]
    exact Ideal.mem_map_of_mem θ (show a s ∈ RingHom.ker w from hwa s)
  have hExtend : ∀ (T : Type u) [CommRing T], _root_.SerrePositivity.IsIntegralPerfectoid T p →
      ∀ i : R →+* T, _root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ ≤ RingHom.ker i →
        ∃ c : _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootFamilyCompletion p ρ →+* T, c.comp qR = i := by
    intro T _ hT i hi
    let i0 := Ideal.Quotient.lift (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ) i hi
    obtain ⟨c, hc, _⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_compatibleRootFamilyCompletionLift_to_perfectoid
      ρ hρ hT i0
    refine ⟨c, ?_⟩
    change c.comp ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap p ρ).comp
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ))) = i
    rw [← RingHom.comp_assoc, hc]
    rfl
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectDeltaPDQuotientEquiv_of_perfectoidExtension D hD d θ hθ hker
    w hw hd (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ) hI qR hqR hExtend β hβ

end SerrePositivity.BhattScholze

end CompatibleRootFamilyPDComparison

/-! ## 任意根族の商の完備化のperfectoid性

tiltの根イデアル商のWitt環を実PD完備化し、標準射を両立させて古典的候補と比較する。
Andréの引用・一般全射性・B5を使わない。
-/

@[expose] public noncomputable section CompatibleRootFamilyCompletionPerfectoid

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type u}

/-- perfectoid環の両立する根をすべて消した商のp完備化はperfectoid。
一般のpねじれと零環も含む。 -/
theorem Semiperfectoid.compatibleRootFamilyCompletion_isIntegralPerfectoid
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (ρ : σ → ℕ → R)
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n) :
    _root_.SerrePositivity.IsIntegralPerfectoid (_root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootFamilyCompletion p ρ) p := by
  let C := _root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootFamilyCompletion p ρ
  let qR := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap p ρ).comp
    (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ))
  rcases subsingleton_or_nontrivial C with hsC | hnC
  · exact Or.inl hsC
  · let := hnC
    rcases hR with hsR | ⟨hpR, hcR, ⟨π, u, hu⟩, hFR, hkerR⟩
    · let := hsR
      let : Subsingleton C := qR.codomain_trivial
      exact Or.inl inferInstance
    · let := hcR
      have hR : _root_.SerrePositivity.IsIntegralPerfectoid R p := Or.inr ⟨hpR, hcR, ⟨π, u, hu⟩, hFR, hkerR⟩
      let : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
      let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletion_isAdicComplete (p := p) ρ
      have hpC : ¬ IsUnit (p : C) := by
        intro h
        let : Subsingleton C := _root_.SerrePositivity.subsingleton_of_isUnit_natCast_of_isHausdorff p C h
        exact zero_ne_one (Subsingleton.elim (0 : C) 1)
      let : Fact (¬ IsUnit (p : C)) := ⟨hpC⟩
      let k := PreTilt R p
      let κ := fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootTilt (ρ s) (hρ s)
      let K := _root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal κ
      let Q := k ⧸ K
      let qk := Ideal.Quotient.mk K
      let L := Perfection.map p (_root_.SerrePositivity.modPMap p qR)
      have hqρ : ∀ s n, qR (ρ s n) = 0 := by
        intro s n
        change algebraMap (R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal ρ) C
          (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal ρ) (ρ s n)) = 0
        have hz : Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.compatibleRootFamilyIdeal ρ) (ρ s n) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(s, n), rfl⟩)
        rw [hz, map_zero]
      have hKL : K ≤ RingHom.ker L := by
        apply Ideal.span_le.mpr
        rintro _ ⟨⟨s, n⟩, rfl⟩
        exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootTiltIdeal_le_ker (ρ s) (hρ s) qR (hqρ s)
          (Ideal.mem_span_range_self (x := n))
      let LQ : Q →+* PreTilt C p := Ideal.Quotient.lift K L hKL
      let : Nontrivial (PreTilt C p) := CharP.nontrivial_of_char_ne_one
        (R := PreTilt C p) (Fact.out : p.Prime).ne_one
      let : Nontrivial Q := LQ.domain_nontrivial
      have hpQ : (p : Q) = 0 := by
        rw [← map_natCast qk, CharP.cast_eq_zero, map_zero]
      let : CharP Q p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpQ
      let : PerfectRing Q p := _root_.SerrePositivity.BhattScholze.compatibleRootFamilyQuotient_perfectRing κ
        (fun s n ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootTilt_pow (ρ s) (hρ s) n)
      let w : WittVector p k →+* WittVector p Q := WittVector.map qk
      have hw : Function.Surjective w := WittVector.map_surjective _ Ideal.Quotient.mk_surjective
      obtain ⟨d, hd, hk⟩ := _root_.SerrePositivity.BhattScholze.exists_distinguished_fontaine_kernel_generator R p hFR hkerR π u hu
      let D := _root_.SerrePositivity.BhattScholze.wittDeltaStructure p Q
      have hD := _root_.SerrePositivity.BhattScholze.wittDeltaStructure_isPerfect p Q
      have hdw : D.IsDistinguished (w d) :=
        (_root_.SerrePositivity.BhattScholze.wittDeltaStructure_map_isDeltaHom p k qk).map_isDistinguished hd
      let β : WittVector p Q →+* C :=
        (WittVector.fontaineTheta C p).comp (WittVector.map LQ)
      have hβ : β.comp w = qR.comp (WittVector.fontaineTheta R p) := by
        have hL : LQ.comp qk = L := rfl
        have hm : (WittVector.map LQ).comp w = WittVector.map L := by
          ext x n
          change LQ (qk (x.coeff n)) = L (x.coeff n)
          exact RingHom.congr_fun hL _
        change ((WittVector.fontaineTheta C p).comp (WittVector.map LQ)).comp w = _
        rw [RingHom.comp_assoc, hm]
        exact _root_.SerrePositivity.BhattScholze.fontaineTheta_natural p qR
      let a : σ → WittVector p k := fun s ↦ WittVector.teichmuller p (κ s 0)
      have ha : ∀ s, WittVector.fontaineTheta R p (a s) = ρ s 0 := by
        intro s
        rw [WittVector.fontaineTheta_teichmuller, _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootTilt_untilt]
      have hwa : ∀ s, w (a s) = 0 := by
        intro s
        change WittVector.map qk (WittVector.teichmuller p (κ s 0)) = 0
        rw [WittVector.map_teichmuller]
        have hqκ : qk (κ s 0) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(s, 0), rfl⟩)
        rw [hqκ, WittVector.teichmuller_zero]
      let := pdCompletionCommRing (WittVector p Q) p (w d)
      obtain ⟨e, _⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_compatibleRootFamilyCompletionPDQuotientEquiv hR ρ hρ D hD d
        (WittVector.fontaineTheta R p) (fun x ↦ surjective_fontaineTheta hFR x) hk
        w hw hdw β hβ a ha hwa
      have hU := (_root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism D hD (w d) hdw).quotient_isIntegralPerfectoid
        (_root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism_isPerfect D hD (w d) hdw)
      exact _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p e.symm hU

/-- 任意根族の最初の元の商の具体的標準射はperfectoid化。 -/
theorem Semiperfectoid.compatibleRootFamilyCompletionMap_isPerfectoidization
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (ρ : σ → ℕ → R)
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n) :
    _root_.SerrePositivity.IsPerfectoidization p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap p ρ) :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletion_isIntegralPerfectoid hR ρ hρ)

/-- 任意根族の最初の元の商の任意の普遍perfectoid化は全射。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_compatibleRootFamily
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (ρ : σ → ℕ → R)
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    {C : Type u} [CommRing C] (f : R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ →+* C)
    (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f := by
  let := hR.isAdicComplete R p
  have h := _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap_isPerfectoidization hR ρ hρ
  exact (h.surjective_iff p hf).mp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletionMap_surjective ρ)

end SerrePositivity.BhattScholze

end CompatibleRootFamilyCompletionPerfectoid

/-! ## B4a：根付き単項商の完備化のperfectoid性

既存の単一根候補と標準射を保ち、一元添字の根族候補との比較からperfectoid性を得る。
Andréの引用・一般全射性・B5を使わない。
-/

@[expose] public noncomputable section CompatibleRootCompletionPerfectoid

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- perfectoid環の両立する根をすべて消した商のp完備化はperfectoid。
一般のpねじれと零環も含む。 -/
theorem Semiperfectoid.compatibleRootCompletion_isIntegralPerfectoid
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    _root_.SerrePositivity.IsIntegralPerfectoid (_root_.SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootCompletion p ρ) p := by
  exact _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootSingletonCompletionEquiv p ρ)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletion_isIntegralPerfectoid hR
      (fun _ : PUnit.{u+1} ↦ ρ) (fun _ ↦ hρ))

/-- 根を持つ単項商の具体的標準射はperfectoid化。 -/
theorem Semiperfectoid.compatibleRootCompletionMap_isPerfectoidization
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    _root_.SerrePositivity.IsPerfectoidization p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap p ρ) :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletion_isIntegralPerfectoid hR ρ hρ)

/-- 根付き単項商の任意の普遍perfectoid化は全射。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_compatibleRoots_unconditional
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {C : Type u} [CommRing C] (f : R ⧸ Ideal.span {ρ 0} →+* C)
    (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_compatibleRoots hR ρ hρ
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootCompletion_isIntegralPerfectoid hR ρ hρ) f hf

end SerrePositivity.BhattScholze

end CompatibleRootCompletionPerfectoid
