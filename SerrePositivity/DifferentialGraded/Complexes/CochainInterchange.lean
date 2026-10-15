module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-! # 符号付き交換則を四つのcochainの合成へ運ぶ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma cochain_quad_interchange {X₀ X₁ X₂ X₃ X₄ Y : Complex A} {p q r s n : ℤ}
    (a : Cochain X₀ X₁ p) (b : Cochain X₁ X₂ q) (c : Cochain X₂ X₃ r)
    (d : Cochain X₃ X₄ s) (e : Cochain X₁ Y r) (f : Cochain Y X₃ q)
    (h : e.comp f (by omega : r + q = q + r) = (q * r).negOnePow • b.comp c rfl)
    (hn : p + q + r + s = n) :
    (a.comp b rfl).comp (c.comp d rfl) (by omega : p + q + (r + s) = n) =
      (q * r).negOnePow • (a.comp e rfl).comp (f.comp d rfl)
        (by omega : p + r + (q + s) = n) := by
  have he := congrArg (fun z : Cochain X₁ X₃ (q + r) =>
    a.comp (z.comp d rfl) (by omega : p + (q + r + s) = n)) h
  rw [Cochain.units_smul_comp, Cochain.comp_units_smul] at he
  have he' := congrArg (fun z => (q * r).negOnePow • z) he
  simp only [smul_smul, Int.units_mul_self, one_smul] at he'
  have h₁ : (a.comp b rfl).comp (c.comp d rfl) (by omega : p + q + (r + s) = n) =
      a.comp ((b.comp c rfl).comp d rfl) (by omega : p + (q + r + s) = n) := by
    rw [Cochain.comp_assoc a b (c.comp d rfl) rfl (by omega : q + (r + s) = q + r + s)
      (by omega), ← Cochain.comp_assoc b c d rfl rfl rfl]
  have h₂ : (a.comp e rfl).comp (f.comp d rfl) (by omega : p + r + (q + s) = n) =
      a.comp ((e.comp f (by omega : r + q = q + r)).comp d rfl)
        (by omega : p + (q + r + s) = n) := by
    rw [Cochain.comp_assoc a e (f.comp d rfl) rfl (by omega : r + (q + s) = q + r + s)
      (by omega), ← Cochain.comp_assoc e f d (by omega : r + q = q + r) rfl
        (by omega : r + q + s = q + r + s)]
  exact h₁.trans (he'.symm.trans (congrArg (fun z => (q * r).negOnePow • z) h₂.symm))

end SerrePositivity.DifferentialGraded
