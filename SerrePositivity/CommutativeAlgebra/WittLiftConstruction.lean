module

public import SerrePositivity.CommutativeAlgebra.WittLiftUniqueness
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-! # 完全標数p環からp進完備環への一意なWitt持上げ -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]
    [Fact (¬ IsUnit (p : A))] [IsAdicComplete (Ideal.span {(p : A)}) A]
    (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- 剰余写像をPerfectionへ持ち上げ、Fontaine θと合成する。 -/
def wittResidueLift (s : k →+* ModP A p) : WittVector p k →+* A :=
  let t : k →+* PreTilt A p := Perfection.lift p k (ModP A p) s
  (WittVector.fontaineTheta A p).comp (WittVector.map t)

/-- Witt持上げのmod p図式。 -/
theorem wittResidueLift_mod_p (s : k →+* ModP A p) :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp (wittResidueLift p A k s) =
      s.comp WittVector.constantCoeff := by
  ext x
  let t : k →+* PreTilt A p := Perfection.lift p k (ModP A p) s
  have hm := WittVector.mk_fontaineTheta (WittVector.map t x)
  rw [WittVector.map_coeff] at hm
  exact hm

/-- 指定した剰余写像のWitt持上げは一意に存在する。 -/
theorem existsUnique_wittResidueLift (s : k →+* ModP A p) :
    ∃! f : WittVector p k →+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f = s.comp WittVector.constantCoeff := by
  refine ⟨wittResidueLift p A k s, wittResidueLift_mod_p p A k s, ?_⟩
  intro f hf
  exact wittLift_unique f (wittResidueLift p A k s)
    (hf.trans (wittResidueLift_mod_p p A k s).symm)

end SerrePositivity
