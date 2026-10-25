module

public import SerrePositivity.BhattScholze.Andre.Remark715.PrincipalPairCompletionRegular

/-!
# André E1・E2：実主完備化の第一剰余

## 概要

実主完備化の H⁰ を標準像の主イデアルで割ると、元の主剰余環と同型になる。
BS Rem 7.15（著者版 p.62）の正則対を完備化へ移す比較。

## 方針

座標を殺す環への実 H⁰ の一意延長から互いに逆の射を作る。

## 規約

正則性・Noether 性を仮定せず、元の標準射を保持する。

## 使われ方

第一完備化の mod p における分母正則性を元の raw 包から移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion

/-- 概要：座標の像が零の環は制限スカラー作用でその座標について導来完備。
方針：一乗のスカラー作用が零であることを使う。
規約：零環も含める。
使われ方：BS Rem 7.15（著者版 p.62）の実主完備化の剰余普遍性。 -/
theorem moduleComplete_of_ringHom_scalar_zero {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (b : R) (hb : g b = 0) :
    let := g.toAlgebra
    IsModuleComplete R b (ModuleCat.of R S) := by
  let := g.toAlgebra
  apply isModuleComplete_of_pow_smul_zero R b (ModuleCat.of R S) 1
  intro x
  change g (b ^ 1) * x = 0
  rw [pow_one, hb, zero_mul]

variable {R : Type u} [CommRing R] (b : R)

/-- 概要：実主完備化 H⁰ の標準座標の主剰余は元の主剰余と環同型。
方針：両剰余で座標が零となることを一意延長へ渡して逆合成を確認する。
規約：正則性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の第一完備化の正則対。 -/
def principalCompletionResidueEquiv :
    letI := principalCompletionCommRing R b
    (PrincipalCompletionH0 R b ⧸ Ideal.span {principalCompletionUnitRingHom R b b}) ≃+*
      R ⧸ Ideal.span {b} := by
  let := principalCompletionCommRing R b
  let H := PrincipalCompletionH0 R b
  let j := principalCompletionUnitRingHom R b
  let I := Ideal.span {b}
  let J := Ideal.span {j b}
  let q := Ideal.Quotient.mk I
  let qH := Ideal.Quotient.mk J
  have hq : q b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b)
  have hqH : qH (j b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (j b))
  let k := (principalCompletion_existsUnique_ringHom R b (R ⧸ I) q
    (moduleComplete_of_ringHom_scalar_zero q b hq)).choose
  have hk : k.comp j = q := (principalCompletion_existsUnique_ringHom R b (R ⧸ I) q
    (moduleComplete_of_ringHom_scalar_zero q b hq)).choose_spec.1
  let F : R ⧸ I →+* H ⧸ J := Ideal.Quotient.lift I (qH.comp j) (by
    change I ≤ RingHom.ker (qH.comp j)
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact hqH)
  let G : H ⧸ J →+* R ⧸ I := Ideal.Quotient.lift J k (by
    change J ≤ RingHom.ker k
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    change k (j b) = 0
    rw [← RingHom.comp_apply, hk]
    exact hq)
  have hGF : G.comp F = RingHom.id (R ⧸ I) := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    change k (j r) = q r
    exact RingHom.congr_fun hk r
  have hFG : F.comp G = RingHom.id (H ⧸ J) := by
    apply Ideal.Quotient.ringHom_ext
    change F.comp k = qH
    have he : (F.comp k).comp j = qH.comp j := by
      rw [RingHom.comp_assoc, hk]
      rfl
    obtain ⟨l, hl, hlu⟩ := principalCompletion_existsUnique_ringHom R b (H ⧸ J) (qH.comp j)
      (moduleComplete_of_ringHom_scalar_zero (qH.comp j) b hqH)
    exact (hlu _ he).trans (hlu _ rfl).symm
  exact RingEquiv.ofRingHom G F hGF hFG

/-- 概要：実主完備化の剰余比較は係数の標準像を元の代表元へ送る。
方針：選択した一意延長の合成仕様を評価する。
規約：任意の元 r を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の第二元正則性の移送。 -/
theorem principalCompletionResidueEquiv_unit (r : R) :
    letI := principalCompletionCommRing R b
    principalCompletionResidueEquiv b
      (Ideal.Quotient.mk _ (principalCompletionUnitRingHom R b r)) =
        Ideal.Quotient.mk (Ideal.span {b}) r := by
  let := principalCompletionCommRing R b
  exact RingHom.congr_fun
    (principalCompletion_existsUnique_ringHom R b (R ⧸ Ideal.span {b})
      (Ideal.Quotient.mk (Ideal.span {b}))
      (moduleComplete_of_ringHom_scalar_zero _ b
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))))).choose_spec.1 r

end SerrePositivity.BhattScholze.Andre
