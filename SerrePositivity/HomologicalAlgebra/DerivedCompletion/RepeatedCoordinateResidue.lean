module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedCoordinate

/-!
# 繰り返した p 座標の完備化の mod p

## 概要
(p,p) 完備化の通常の mod p は元の環の mod p と標準同型。

## 方針
剰余の完備性と完備化の環としての普遍性で互いに逆の射を作る。

## 規約
p 正則性は仮定しない。

## 使われ方
BS 著者版 Construction 6.1 の被覆の剰余の計算。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory

variable (R : Type u) [CommRing R] (p : ℕ)

private def repeatedModPComparison :
    letI := pdCompletionCommRing R p (p : R)
    {e : (PDCompletionH0 R p (p : R) ⧸ Ideal.span {(p : PDCompletionH0 R p (p : R))}) ≃+*
        (R ⧸ Ideal.span {(p : R)}) //
      ∀ x : R, e (Ideal.Quotient.mk _ (pdCompletionUnit R p (p : R) x)) =
        Ideal.Quotient.mk _ x} := by
  let C := PDCompletionH0 R p (p : R)
  letI : CommRing C := pdCompletionCommRing R p (p : R)
  let Q := R ⧸ Ideal.span {(p : R)}
  let T := C ⧸ Ideal.span {(p : C)}
  let j : R →+* C := pdCompletionUnit R p (p : R)
  let q : R →+* Q := Ideal.Quotient.mk _
  let π : C →+* T := Ideal.Quotient.mk _
  have hpQ : (p : Q) = 0 := by
    simpa only [map_natCast] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : R)))
  have hpT : (p : T) = 0 := by
    simpa only [map_natCast] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : C)))
  have hcQ : IsModuleComplete Q (p : Q) (ModuleCat.of Q Q) := by
    rw [hpQ]
    exact isModuleComplete_zero Q _
  have hcT : IsModuleComplete T (p : T) (ModuleCat.of T T) := by
    rw [hpT]
    exact isModuleComplete_zero T _
  have hqComplete : letI := q.toAlgebra
      IsModuleComplete R (p : R) (ModuleCat.of R Q) := by
    letI := q.toAlgebra
    apply (isModuleComplete_algebraMap_iff R Q (p : R) Q).mp
    simpa only [map_natCast] using hcQ
  let F := pdCompletion_existsUnique_ringHom R p (p : R) Q q hqComplete hqComplete
  let f := F.choose
  have hf : f.comp j = q := F.choose_spec.1
  let f₀ : T →+* Q := Ideal.Quotient.lift _ f (by
    change Ideal.span {(p : C)} ≤ RingHom.ker f
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast]
    exact hpQ)
  let g₀ : Q →+* T := Ideal.Quotient.lift _ (π.comp j) (by
    change Ideal.span {(p : R)} ≤ RingHom.ker (π.comp j)
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, RingHom.comp_apply, map_natCast,
      map_natCast]
    exact hpT)
  have hfg : f₀.comp g₀ = RingHom.id Q := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact RingHom.congr_fun hf x
  have hgf : g₀.comp f₀ = RingHom.id T := by
    apply Ideal.Quotient.ringHom_ext
    have hTComplete : letI := (π.comp j).toAlgebra
        IsModuleComplete R (p : R) (ModuleCat.of R T) := by
      letI := (π.comp j).toAlgebra
      apply (isModuleComplete_algebraMap_iff R T (p : R) T).mp
      simpa only [map_natCast] using hcT
    have hu := pdCompletion_existsUnique_ringHom R p (p : R) T (π.comp j)
      hTComplete hTComplete
    change (g₀.comp f₀).comp π = π
    apply hu.unique
    · ext x
      change g₀ (f (j x)) = π (j x)
      have hfx : f (j x) = q x := RingHom.congr_fun hf x
      rw [hfx]
      rfl
    · rfl
  exact ⟨RingEquiv.ofRingHom f₀ g₀ hfg hgf, fun x => RingHom.congr_fun hf x⟩

/-- 概要：(p,p) 完備化の mod p と元の環の mod p の標準同型。
方針：剰余環への完備化の普遍性を使う。
規約：実際の零次完備化環の通常商。
使われ方：BS 著者版 Construction 6.1 の式 (6) の標的。 -/
def repeatedCompletionModPEquiv :
    letI := pdCompletionCommRing R p (p : R)
    (PDCompletionH0 R p (p : R) ⧸ Ideal.span {(p : PDCompletionH0 R p (p : R))}) ≃+*
      (R ⧸ Ideal.span {(p : R)}) :=
  (repeatedModPComparison R p).val

/-- 剰余比較は標準係数脚を保つ。 -/
theorem repeatedCompletionModPEquiv_unit (x : R) :
    letI := pdCompletionCommRing R p (p : R)
    repeatedCompletionModPEquiv R p (Ideal.Quotient.mk _ (pdCompletionUnit R p (p : R) x)) =
      Ideal.Quotient.mk _ x :=
  (repeatedModPComparison R p).property x

end SerrePositivity.DerivedCompletion
