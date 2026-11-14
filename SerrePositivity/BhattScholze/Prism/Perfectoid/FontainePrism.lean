module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidWittEquiv
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure

/-!
# 固定した Fontaine Witt 環上の完全 prism

## 概要
完全 prism の剰余表示を W(R♭) 上へ戻し、δ 構造と θ の一致も返す。
## 方針
Witt 復元の環同型で生成元と二つの完備性を移す。
## 規約
BS 著者版 Theorem 3.10・Proposition 7.10。ここでは p が非単元である枝。
## 使われ方
drafts の AinfData の古典的な存在。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open DerivedCompletion Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {R A : Type u} [CommRing R] [CommRing A]
  [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R]

/-- 固定した Witt δ 環上へ完全 prism を移し、標準 Fontaine 射を剰余射として実現する。 -/
theorem exists_fontainePrism_of_perfectPresentation (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) (hb : IsBoundedPrism P) (e : A ⧸ P.ideal ≃+* R) :
    ∃ Q : OrientedPrism p (WittVector p (PreTilt R p)),
      Q.deltaStructure = wittDeltaStructure p (PreTilt R p) ∧
      Q.deltaStructure.IsPerfect ∧ IsBoundedPrism Q ∧
      ∃ res : WittVector p (PreTilt R p) ⧸ Q.ideal ≃+* R,
        res.toRingHom.comp (Ideal.Quotient.mk Q.ideal) = WittVector.fontaineTheta R p := by
  obtain ⟨ρ, hρ, hθ⟩ := exists_fontaineCompatibleWittEquiv p P hP e
  let W := WittVector p (PreTilt R p)
  let D := wittDeltaStructure p (PreTilt R p)
  let d : W := ρ.symm P.generator
  have hd : D.IsDistinguished d := hρ.symm.map_isDistinguished P.isDistinguished_generator
  have hgen : ρ d = P.generator := ρ.apply_symm_apply _
  have hreg : Function.Injective (fun x : W => d * x) := by
    intro x y hxy
    apply ρ.injective
    apply P.generator_regular
    simpa only [map_mul, hgen] using congrArg ρ hxy
  letI : IsAdicComplete (Ideal.span {(p : W)}) W := by
    have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {(p : A)}) ρ.symm).mpr
      (P.isAdicComplete_p_of_perfect hP)
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h
  letI : IsAdicComplete (Ideal.span {d}) W := by
    have h := (IsAdicComplete.congr_ringEquiv P.ideal ρ.symm).mpr P.isAdicComplete_generator
    simpa only [OrientedPrism.ideal, Ideal.map_span, Set.image_singleton] using h
  let Q := OrientedPrism.ofDistinguished D d hd hreg
    (isModuleComplete_of_isAdicComplete W (p : W) (ModuleCat.of W W))
    (isModuleComplete_of_isAdicComplete W d (ModuleCat.of W W))
  have hmap : Q.ideal.map ρ.toRingHom = P.ideal := by
    change (Ideal.span {d}).map ρ.toRingHom = Ideal.span {P.generator}
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {ρ d} = _
    rw [hgen]
  let eP := Ideal.quotientEquiv Q.ideal P.ideal ρ hmap.symm
  have hbound : IsBoundedPrism Q := by
    obtain ⟨N, hN⟩ := hb
    refine ⟨N, fun n x hx => ?_⟩
    apply eP.injective
    have hx' : (p : A ⧸ P.ideal)^n * eP x = 0 := by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg eP hx
    simpa only [map_mul, map_pow, map_natCast, map_zero] using hN n (eP x) hx'
  refine ⟨Q, rfl, wittDeltaStructure_isPerfect p (PreTilt R p), hbound, eP.trans e, ?_⟩
  apply RingHom.ext
  intro x
  change e (Ideal.Quotient.mk P.ideal (ρ x)) = WittVector.fontaineTheta R p x
  exact RingHom.congr_fun hθ x

end SerrePositivity.BhattScholze.Semiperfectoid
