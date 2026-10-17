module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotients of a specified universal perfectoidization

The closed side of an excision diagram can be built from quotients of the
specified perfectoid targets. Its universal property refers to the original
source quotient and the original induced quotient map.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.IsPerfectoidization
variable {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime] {f : A →+* C}

/-- Perfectoidizing the quotient of C by the image of J also perfectoidizes A/J,
through the actual induced quotient map of the original universal unit. -/
theorem quotient_map (hf : IsPerfectoidization p f) (J : Ideal A)
    (h : C ⧸ J.map f →+* D) (hh : IsPerfectoidization p h) :
    IsPerfectoidization p
      (h.comp (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)) := by
  refine ⟨hh.1, ?_⟩
  intro T _ hT k
  let a : A →+* A ⧸ J := Ideal.Quotient.mk J
  let c : C →+* C ⧸ J.map f := Ideal.Quotient.mk (J.map f)
  obtain ⟨l, hl, hu⟩ := hf.2 T hT (k.comp a)
  have hker : J.map f ≤ RingHom.ker l := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change l (f x) = 0
    have he := RingHom.congr_fun hl x
    change l (f x) = k (a x) at he
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at he
    exact he
  let q : C ⧸ J.map f →+* T := Ideal.Quotient.lift _ l (fun x hx => hker hx)
  obtain ⟨L, hL, huniq⟩ := hh.2 T hT q
  have hLk : L.comp (h.comp (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)) = k := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    change L (h (c (f x))) = k (a x)
    exact (RingHom.congr_fun hL (c (f x))).trans (RingHom.congr_fun hl x)
  refine ⟨L, hLk, ?_⟩
  intro m hm
  apply huniq
  apply Ideal.Quotient.ringHom_ext
  change (m.comp h).comp c = l
  apply hu
  ext x
  exact RingHom.congr_fun hm (a x)

end SerrePositivity.IsPerfectoidization
