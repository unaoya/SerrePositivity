module

public import SerrePositivity.BhattScholze.DeltaDivisionUniversal
public import SerrePositivity.BhattScholze.DeltaPDCompletionUniversal

/-!
# André E1・E2：元の raw δ 割り算包の実完備化の普遍性

## 概要

分母の像が正則で分子族がその像で割り切れる δ 射は、元の raw 包の実完備化から
一意に延長する。BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の envelope 比較への入口。

## 方針

正則分母への raw δ 割り算の一意延長と、実二座標完備化の δ 一意延長を合成する。

## 規約

元の raw 包をねじれ除去商へ変更しない。試験環の p と分母像の導来完備性を明示する。

## 使われ方

具体的な実完備化 prism の普遍性を、基底射を保った比較へ接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R σ T : Type u} [CommRing R] [CommRing T]

/-- 概要：正則な分母像と分子の可除性を持つ完備 δ 試験環へ、raw 実完備化から一意に延長する。
方針：raw δ 割り算と実完備化の二つの一意延長を結ぶ。
規約：試験環の p ねじれを制限せず、分母の正則性を明示する。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の元の envelope の比較。 -/
theorem existsUnique_rawDeltaDivisionPDHom
    (D : DeltaStructure p R) (E : DeltaStructure p T) (d : R) (a : σ → R)
    (f : R →+* T) (hf : D.IsDeltaHom E f)
    (hreg : Function.Injective (fun x : T => f d * x)) (ha : ∀ s, f d ∣ f (a s))
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (f d) (ModuleCat.of T T)) :
    let B := DeltaAdjoinDivision D d a
    let j := deltaAdjoinDivisionMap D d a
    let := pdCompletionCommRing B p (j d)
    ∃! h : PDCompletionH0 B p (j d) →+* T,
      (deltaPDCompletionStructure (deltaAdjoinDivisionStructure D d a) (j d)).IsDeltaHom E h ∧
        h.comp ((pdCompletionUnit B p (j d)).comp j) = f := by
  let B := DeltaAdjoinDivision D d a
  let DB := deltaAdjoinDivisionStructure D d a
  let j := deltaAdjoinDivisionMap D d a
  let := pdCompletionCommRing B p (j d)
  let c := pdCompletionUnit B p (j d)
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D E d a f hf hreg ha
  have hkd : k (j d) = f d := RingHom.congr_fun hk.2 d
  have hd' : IsModuleComplete T (k (j d)) (ModuleCat.of T T) := by rw [hkd]; exact hd
  obtain ⟨h, hh, hu⟩ := existsUnique_deltaPDCompletionHom DB (j d) E k hk.1 hp hd'
  refine ⟨h, ⟨hh.1, ?_⟩, ?_⟩
  · change h.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hh.2, hk.2]
  · intro l hl
    apply hu l
    refine ⟨hl.1, ?_⟩
    apply hku (l.comp c)
    refine ⟨hl.1.comp (pdCompletionUnit_isDeltaHom DB (j d)), ?_⟩
    change (l.comp c).comp j = f
    rw [RingHom.comp_assoc]
    exact hl.2

end SerrePositivity.BhattScholze.Andre
