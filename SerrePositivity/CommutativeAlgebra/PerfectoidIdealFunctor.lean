module
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationMap

/-! # Original quotient perfectoidizations and their kernel ideals under base maps

These maps retain the chosen B3 objects and their original quotient units.
No flatness or perfectoidization base-change isomorphism is asserted.
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable {R S : Type u} [CommRing R] [CommRing S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hS : IsIntegralPerfectoid S p) (φ : R →+* S)

/-- The induced map of the original chosen quotient perfectoidizations. -/
def quotientPerfectoidizationMap (I : Ideal R) (J : Ideal S) (hIJ : I ≤ J.comap φ) :
    QuotientPerfectoidization R I p hR →+* QuotientPerfectoidization S J p hS :=
  IsPerfectoidization.map (isPerfectoidization_toQuotientPerfectoidization R I p hR)
    (isPerfectoidization_toQuotientPerfectoidization S J p hS)
    (Ideal.quotientMap J φ hIJ)

/-- The induced map commutes with the original quotient perfectoidization units. -/
theorem quotientPerfectoidizationMap_comp (I : Ideal R) (J : Ideal S)
    (hIJ : I ≤ J.comap φ) :
    (quotientPerfectoidizationMap p hR hS φ I J hIJ).comp
      (toQuotientPerfectoidization R I p hR) =
    (toQuotientPerfectoidization S J p hS).comp (Ideal.quotientMap J φ hIJ) :=
  IsPerfectoidization.map_comp _ _ _

/-- In particular the base-ring representatives retain their original images. -/
@[simp] theorem quotientPerfectoidizationMap_mk (I : Ideal R) (J : Ideal S)
    (hIJ : I ≤ J.comap φ) (x : R) :
    quotientPerfectoidizationMap p hR hS φ I J hIJ
      (toQuotientPerfectoidization R I p hR (Ideal.Quotient.mk I x)) =
      toQuotientPerfectoidization S J p hS (Ideal.Quotient.mk J (φ x)) := by
  exact RingHom.congr_fun (quotientPerfectoidizationMap_comp p hR hS φ I J hIJ)
    (Ideal.Quotient.mk I x)

/-- The original perfectoid ideal maps into the ideal of the image generator. -/
theorem perfectoidIdeal_map_le (g : R) :
    (perfectoidIdeal R p hR g).map φ ≤ perfectoidIdeal S p hS (φ g) := by
  apply Ideal.map_le_iff_le_comap.mpr
  have hIJ : Ideal.span {g} ≤ (Ideal.span {φ g}).comap φ := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  intro x hx
  change toQuotientPerfectoidization R (Ideal.span {g}) p hR
    (Ideal.Quotient.mk (Ideal.span {g}) x) = 0 at hx
  change toQuotientPerfectoidization S (Ideal.span {φ g}) p hS
    (Ideal.Quotient.mk (Ideal.span {φ g}) (φ x)) = 0
  have he := quotientPerfectoidizationMap_mk p hR hS φ
    (Ideal.span {g}) (Ideal.span {φ g}) hIJ x
  rw [hx, map_zero] at he
  exact he.symm

/-- Every original almost scalar remains an almost scalar after the base map. -/
theorem map_mem_perfectoidIdeal (g x : R) (hx : x ∈ perfectoidIdeal R p hR g) :
    φ x ∈ perfectoidIdeal S p hS (φ g) :=
  perfectoidIdeal_map_le p hR hS φ g (Ideal.mem_map_of_mem φ hx)

/-- The map on the actual kernel quotients uses precisely the original base map. -/
def perfectoidIdealQuotientMap (g : R) :
    R ⧸ perfectoidIdeal R p hR g →+* S ⧸ perfectoidIdeal S p hS (φ g) :=
  Ideal.quotientMap _ φ
    (Ideal.map_le_iff_le_comap.mp (perfectoidIdeal_map_le p hR hS φ g))

@[simp] theorem perfectoidIdealQuotientMap_mk (g x : R) :
    perfectoidIdealQuotientMap p hR hS φ g
      (Ideal.Quotient.mk (perfectoidIdeal R p hR g) x) =
      Ideal.Quotient.mk (perfectoidIdeal S p hS (φ g)) (φ x) := rfl

end SerrePositivity
