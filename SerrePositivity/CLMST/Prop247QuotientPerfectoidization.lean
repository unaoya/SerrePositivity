module

public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationCompletion
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity

/-! # Prop 2.4.7：原典の像の商の指定 perfectoid 化への全射性

任意の全射商を一度古典的に p 完備化し、既存 B4 へ渡す。
元の商の有限表示性・分離性・完備性は追加しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- perfectoid 環の任意の全射商の指定 perfectoid 化写像は全射である。
商の完備性を仮定せず、元の全射から前完備性を供給して既存 B4 を適用する。 -/
theorem prop247_surjective_perfectoidization_of_quotient
    {R A T : Type u} [CommRing R] [CommRing A] [CommRing T]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (q : R →+* A) (hq : Function.Surjective q)
    (f : A →+* T) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  letI : Algebra R A := q.toAlgebra
  letI := hR.isAdicComplete R p
  have hpre : IsPrecomplete (Ideal.span {(p : R)}) A :=
    isPrecomplete_of_surjective (Ideal.span {(p : R)}) (Algebra.linearMap R A) hq
  letI : IsPrecomplete (Ideal.span {(p : A)}) A := by
    rw [← pIdeal_map R A p (algebraMap R A)]
    exact (IsPrecomplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (M := A)).mpr hpre
  let C := AdicCompletion (Ideal.span {(p : A)}) A
  let a := algebraMap A C
  have ha : Function.Surjective a := AdicCompletion.of_surjective (Ideal.span {(p : A)}) A
  have hc : IsAdicComplete (Ideal.span {(p : A)}) C :=
    AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : A))
  letI : IsAdicComplete (Ideal.span {(p : C)}) C := by
    rw [← pIdeal_map A C p a]
    exact (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : A)}) (M := C)).mpr hc
  have hfc : Function.Surjective (IsPerfectoidization.completionMap p hf) :=
    BhattScholze.surjective_of_isPerfectoidization_of_adic_complete_quotient hR
      (a.comp q) (ha.comp hq) (IsPerfectoidization.completionMap p hf)
      (IsPerfectoidization.to_completion p hf)
  intro t
  obtain ⟨c, hct⟩ := hfc t
  obtain ⟨x, hxc⟩ := ha c
  refine ⟨x, ?_⟩
  calc
    f x = IsPerfectoidization.completionMap p hf (a x) :=
      (RingHom.congr_fun (IsPerfectoidization.completionMap_comp p hf) x).symm
    _ = t := by rw [hxc]; exact hct

end SerrePositivity.CLMST
