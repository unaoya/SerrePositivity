module

public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Completion
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity

/-! # 全射な商の指定した perfectoid 化

## 概要

全射な商を一度古典的に p 完備化してから BS の B4 へ渡し、指定した perfectoid 化への写像が全射であることを示す（`surjective_perfectoidization_of_quotient`）。
BS 著者版 Corollary 7.3 の普遍 perfectoid 化を、指定した全射商について構成する。

## 規約

元の商の有限表示性・分離性・完備性は仮定しない。旧 `CLMST/Prop247QuotientPerfectoidization`（`prop247_` を外した）。

## 使われ方

CLMST の Prop 2.4.7 の階数の像の perfectoid 化。
-/

@[expose] public noncomputable section

universe u

section QuotientPerfectoidizationPart

namespace SerrePositivity.BhattScholze
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- perfectoid 環の任意の全射商の指定 perfectoid 化写像は全射である。
商の完備性を仮定せず、元の全射から前完備性を供給して既存 B4 を適用する。 -/
theorem Semiperfectoid.surjective_perfectoidization_of_quotient
    {R A T : Type u} [CommRing R] [CommRing A] [CommRing T]
    (p : ℕ) [Fact p.Prime] (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p)
    (q : R →+* A) (hq : Function.Surjective q)
    (f : A →+* T) (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f := by
  letI : Algebra R A := q.toAlgebra
  letI := hR.isAdicComplete R p
  have hpre : IsPrecomplete (Ideal.span {(p : R)}) A :=
    _root_.SerrePositivity.isPrecomplete_of_surjective (Ideal.span {(p : R)}) (Algebra.linearMap R A) hq
  letI : IsPrecomplete (Ideal.span {(p : A)}) A := by
    rw [← _root_.SerrePositivity.pIdeal_map R A p (algebraMap R A)]
    exact (IsPrecomplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (M := A)).mpr hpre
  let C := AdicCompletion (Ideal.span {(p : A)}) A
  let a := algebraMap A C
  have ha : Function.Surjective a := AdicCompletion.of_surjective (Ideal.span {(p : A)}) A
  have hc : IsAdicComplete (Ideal.span {(p : A)}) C :=
    AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : A))
  letI : IsAdicComplete (Ideal.span {(p : C)}) C := by
    rw [← _root_.SerrePositivity.pIdeal_map A C p a]
    exact (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : A)}) (M := C)).mpr hc
  have hfc : Function.Surjective (_root_.SerrePositivity.IsPerfectoidization.completionMap p hf) :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_adic_complete_quotient hR
      (a.comp q) (ha.comp hq) (_root_.SerrePositivity.IsPerfectoidization.completionMap p hf)
      (_root_.SerrePositivity.IsPerfectoidization.to_completion p hf)
  intro t
  obtain ⟨c, hct⟩ := hfc t
  obtain ⟨x, hxc⟩ := ha c
  refine ⟨x, ?_⟩
  calc
    f x = _root_.SerrePositivity.IsPerfectoidization.completionMap p hf (a x) :=
      (RingHom.congr_fun (_root_.SerrePositivity.IsPerfectoidization.completionMap_comp p hf) x).symm
    _ = t := by rw [hxc]; exact hct

end SerrePositivity.BhattScholze

end QuotientPerfectoidizationPart
