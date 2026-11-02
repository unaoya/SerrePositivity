module

public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-! # 整 perfectoid 環と perfectoid 化の普遍性

CLMST Definition 2.4.1 の四条件を、Mathlib の完備性と Fontaine の写像で定義する。
perfectoid 化は、perfectoid 環への写像の普遍性として表す。
長さや Koszul ホモロジーに関する仮定はこれらの定義に含めない。
-/

@[expose] public section

universe u

namespace SerrePositivity

/-- 整 perfectoid 環：`p` 進完備、`p` は単元倍の `p` 乗、剰余 Frobenius は全射、
Fontaine の写像の核は単項。CLMST Definition 2.4.1。
零環も含める。Mathlib の Fontaine 写像が `p` の非可逆性を要求するため、
零環を別の場合として記す（非零の `p` 進完備環では `p` は非可逆）。 -/
def IsIntegralPerfectoid (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] : Prop :=
  Subsingleton S ∨ ∃ (hp : ¬ IsUnit (p : S))
    (hc : IsAdicComplete (Ideal.span {(p : S)}) S),
    (∃ (ϖ : S) (a : Sˣ), (p : S) = a * ϖ ^ p) ∧
    Function.Surjective (fun x : S ⧸ Ideal.span {(p : S)} ↦ x ^ p) ∧
    (letI : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
     letI := hc
     (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)

/-- `f : S → C` が perfectoid 化であるという普遍性。
`C` は perfectoid で、任意の perfectoid 環への写像が一意に `f` を経由する。 -/
def IsPerfectoidization {S C : Type u} [CommRing S] [CommRing C]
    (p : ℕ) [Fact p.Prime] (f : S →+* C) : Prop :=
  IsIntegralPerfectoid C p ∧
    ∀ (T : Type u) [CommRing T], IsIntegralPerfectoid T p →
      ∀ g : S →+* T, ∃! l : C →+* T, l.comp f = g

end SerrePositivity

section ComposeRingEquivPart

namespace SerrePositivity

/-- perfectoid 化の普遍性は、始域の環同型に沿う前合成で保たれる。 -/
theorem IsPerfectoidization.comp_ringEquiv {S S' C : Type u}
    [CommRing S] [CommRing S'] [CommRing C]
    {p : ℕ} [Fact p.Prime] {f : S →+* C}
    (hf : IsPerfectoidization p f) (e : S' ≃+* S) :
    IsPerfectoidization p (f.comp e.toRingHom) := by
  refine ⟨hf.1, ?_⟩
  intro T _ hT g
  obtain ⟨l, hl, hu⟩ := hf.2 T hT (g.comp e.symm.toRingHom)
  refine ⟨l, ?_, ?_⟩
  · ext x
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using
      DFunLike.congr_fun hl (e x)
  · intro l' hl'
    apply hu l'
    ext x
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using
      DFunLike.congr_fun hl' (e.symm x)

end SerrePositivity

end ComposeRingEquivPart
