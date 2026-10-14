module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid

/-! # untiltと環準同型の両立

各成分の持ち上げのp冪乗の合同を写し、分離性によってuntiltの自然性を確認する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) [Fact p.Prime]

def modPMap (f : R →+* S) : ModP R p →+* ModP S p :=
  Ideal.quotientMap (Ideal.span {(p : S)}) f (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _))

variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- p進完備な環間の環準同型はuntiltと可換する。 -/
theorem untilt_map (f : R →+* S) (x : PreTilt R p) :
    PreTilt.untilt (Perfection.map p (modPMap p f) x) = f x.untilt := by
  change Perfection.teichmullerFun (Perfection.map p (modPMap p f) x) = f x.untilt
  apply Perfection.teichmullerFun_spec
  intro n
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  refine ⟨f z, ?_, ?_⟩
  · change Ideal.Quotient.mk (Ideal.span {(p : S)}) (f z) =
      modPMap p f (PreTilt.coeff n x)
    rw [← hz]
    rfl
  · have h := Perfection.teichmullerFun_sModEq hz
    have hm := Ideal.mem_map_of_mem f (SModEq.sub_mem.mp h.symm)
    apply SModEq.sub_mem.mpr
    rw [show x.untilt = Perfection.teichmullerFun x from rfl]
    simpa only [Ideal.map_pow, Ideal.map_span, Set.image_singleton,
      map_natCast, map_sub, map_pow] using hm

end SerrePositivity
