module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealFunctor
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealCover

/-! # The actual four universal maps of an excision diagram

The closed sides are chosen by B3 from quotients of the specified perfectoid
rings. Their units are universal for the original source quotients as well.
Only commutativity and identification of these actual maps are proved here;
no excision or pullback assertion is added as an input or inferred.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime] {f : A →+* C} {g : B →+* D}

/-- The closed-side unit from the original source quotient. -/
def perfectoidizationClosedSideUnit (hf : IsPerfectoidization p f) (J : Ideal A) :
    A ⧸ J →+* QuotientPerfectoidization C (J.map f) p hf.1 :=
  (toQuotientPerfectoidization C (J.map f) p hf.1).comp
    (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)

/-- This exact unit is universal for the original source quotient. -/
theorem perfectoidizationClosedSideUnit_isPerfectoidization
    (hf : IsPerfectoidization p f) (J : Ideal A) :
    IsPerfectoidization p (perfectoidizationClosedSideUnit hf J) :=
  hf.quotient_map J (toQuotientPerfectoidization C (J.map f) p hf.1)
    (isPerfectoidization_toQuotientPerfectoidization C (J.map f) p hf.1)

/-- The vertical map starts at the specified perfectoid ring, not at a replacement model. -/
def perfectoidizationClosedSideProjection (hf : IsPerfectoidization p f) (J : Ideal A) :
    C →+* QuotientPerfectoidization C (J.map f) p hf.1 :=
  (toQuotientPerfectoidization C (J.map f) p hf.1).comp (Ideal.Quotient.mk (J.map f))

/-- The original unit square commutes on the entire source ring. -/
theorem perfectoidizationClosedSideProjection_comp
    (hf : IsPerfectoidization p f) (J : Ideal A) :
    (perfectoidizationClosedSideProjection hf J).comp f =
      (perfectoidizationClosedSideUnit hf J).comp (Ideal.Quotient.mk J) := rfl

/-- The vertical map kills the images of all original members of the ideal. -/
theorem perfectoidizationClosedSideProjection_eq_zero_of_mem
    (hf : IsPerfectoidization p f) (J : Ideal A) (x : A) (hx : x ∈ J) :
    perfectoidizationClosedSideProjection hf J (f x) = 0 := by
  change toQuotientPerfectoidization C (J.map f) p hf.1
    (Ideal.Quotient.mk (J.map f) (f x)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hx), map_zero]

/-- The original base perfectoid ideal is killed on the closed side, through
exactly the original coefficient map and the original quotient unit. -/
theorem perfectoidizationClosedSideProjection_originalIdeal
    {R : Type u} [CommRing R] (hR : IsIntegralPerfectoid R p) (α : R →+* A)
    (hf : IsPerfectoidization p f) (J : Ideal A) (a : R) (ha : α a ∈ J) :
    ∀ s ∈ perfectoidIdeal R p hR a,
      perfectoidizationClosedSideProjection hf J (f (α s)) = 0 := by
  let k := (perfectoidizationClosedSideProjection hf J).comp (f.comp α)
  have hk : k a = 0 := perfectoidizationClosedSideProjection_eq_zero_of_mem hf J (α a) ha
  exact perfectoidIdeal_le_ker_of_eq_zero R p hR
    (isPerfectoidization_toQuotientPerfectoidization C (J.map f) p hf.1).1 k a hk

/-- The actual functorial top map sends the original closed-side ideal into its image. -/
theorem perfectoidizationClosedComparison_ideal_le
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    J.map f ≤ ((J.map q).map g).comap (IsPerfectoidization.map hf hg q) := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_map, hf.map_comp hg q, ← Ideal.map_map]

/-- The lower horizontal map between the actual B3 closed-side objects. -/
def perfectoidizationClosedComparison
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    QuotientPerfectoidization C (J.map f) p hf.1 →+*
      QuotientPerfectoidization D ((J.map q).map g) p hg.1 :=
  quotientPerfectoidizationMap p hf.1 hg.1 (IsPerfectoidization.map hf hg q)
    (J.map f) ((J.map q).map g) (perfectoidizationClosedComparison_ideal_le hf hg q J)

/-- The actual perfectoidization excision square commutes. This is not a pullback assertion. -/
theorem perfectoidizationClosedComparison_square
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    (perfectoidizationClosedComparison hf hg q J).comp
        (perfectoidizationClosedSideProjection hf J) =
      (perfectoidizationClosedSideProjection hg (J.map q)).comp
        (IsPerfectoidization.map hf hg q) := by
  ext x
  exact quotientPerfectoidizationMap_mk p hf.1 hg.1 (IsPerfectoidization.map hf hg q)
    (J.map f) ((J.map q).map g) (perfectoidizationClosedComparison_ideal_le hf hg q J) x

/-- The lower horizontal map retains the original quotient units and quotient map. -/
theorem perfectoidizationClosedComparison_unit
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    (perfectoidizationClosedComparison hf hg q J).comp
        (perfectoidizationClosedSideUnit hf J) =
      (perfectoidizationClosedSideUnit hg (J.map q)).comp
        (Ideal.quotientMap (J.map q) q Ideal.le_comap_map) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  have hs := RingHom.congr_fun (perfectoidizationClosedComparison_square hf hg q J) (f x)
  have hm : IsPerfectoidization.map hf hg q (f x) = g (q x) :=
    RingHom.congr_fun (hf.map_comp hg q) x
  change perfectoidizationClosedComparison hf hg q J
      (perfectoidizationClosedSideProjection hf J (f x)) =
    perfectoidizationClosedSideProjection hg (J.map q) (g (q x))
  change perfectoidizationClosedComparison hf hg q J
      (perfectoidizationClosedSideProjection hf J (f x)) =
    perfectoidizationClosedSideProjection hg (J.map q)
      (IsPerfectoidization.map hf hg q (f x)) at hs
  rw [hm] at hs
  exact hs

/-- The constructed lower map is precisely the functorial map for the original quotients. -/
theorem perfectoidizationClosedComparison_eq_map
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    perfectoidizationClosedComparison hf hg q J =
      IsPerfectoidization.map (perfectoidizationClosedSideUnit_isPerfectoidization hf J)
        (perfectoidizationClosedSideUnit_isPerfectoidization hg (J.map q))
        (Ideal.quotientMap (J.map q) q Ideal.le_comap_map) :=
  IsPerfectoidization.lift_unique (perfectoidizationClosedSideUnit_isPerfectoidization hf J)
    (perfectoidizationClosedSideUnit_isPerfectoidization hg (J.map q)).1 _ _
    (perfectoidizationClosedComparison_unit hf hg q J)

end SerrePositivity.BhattScholze
