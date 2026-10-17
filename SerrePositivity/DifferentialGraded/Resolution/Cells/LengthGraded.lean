module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.LengthTransition
public import SerrePositivity.DifferentialGraded.Complexes.PerturbationMap

/-! # 固定長pathの次数付き商：境界置換は商で消える -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

def exactLengthSet (n : ℕ) : Set (List I) := {w | w.length = n}

/-- 固定長pathには内部微分だけを置く。 -/
abbrev exactLengthHom (n : ℕ) (x y : D) : Complex A :=
  ComplexCoproduct.subfamily (fun w => C.term A D I w x y) (exactLengthSet I n)

def exactLengthProjection (n : ℕ) (x y : D) :
    C.internalHom A D I x y ⟶ C.exactLengthHom A D I n x y :=
  ComplexCoproduct.projection (fun w => C.term A D I w x y) (exactLengthSet I n)

lemma replaceSummand_exactLength_projection (n : ℕ) (x y : D)
    (w : List I) (hw : w.length ≤ n) (j : ℕ) (hj : j < w.length) :
    (C.replaceSummand A D I w j x y).comp
      (Cochain.ofHom (C.exactLengthProjection A D I n x y)) (add_zero 1) = 0 := by
  have hn : w.eraseIdx j ∉ exactLengthSet I n := by
    change (w.eraseIdx j).length ≠ n
    rw [List.length_eraseIdx_of_lt hj]
    omega
  have h : C.inclusion A D I (w.eraseIdx j) x y ≫
      C.exactLengthProjection A D I n x y = 0 :=
    ComplexCoproduct.ι_projection_not_mem (fun w : List I => C.term A D I w x y)
      (exactLengthSet I n) (w.eraseIdx j) hn
  rw [replaceSummand, Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    h, Cochain.ofHom_zero, Cochain.comp_zero]

lemma replaceRow_exactLength_projection (n : ℕ) (x y : D) (w : List I) (hw : w.length ≤ n) :
    (C.replaceRow A D I w x y).comp
      (Cochain.ofHom (C.exactLengthProjection A D I n x y)) (add_zero 1) = 0 := by
  let R : Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 →+
      Cochain (C.term A D I w x y) (C.exactLengthHom A D I n x y) 1 :=
    { toFun := fun f => f.comp (Cochain.ofHom (C.exactLengthProjection A D I n x y)) (add_zero 1)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun f g => Cochain.add_comp f g _ _ }
  change R (∑ j ∈ Finset.range w.length, C.replaceSummand A D I w j x y) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  exact C.replaceSummand_exactLength_projection A D I n x y w hw j (Finset.mem_range.mp hj)

def lengthInternalQuotient (n : ℕ) (x y : D) :
    C.lengthInternalHom A D I n x y ⟶ C.exactLengthHom A D I n x y :=
  ComplexCoproduct.select (fun w => C.term A D I w x y) (lengthSet I n) (exactLengthSet I n)

lemma lengthReplacement_quotient_zero (n : ℕ) (x y : D) :
    (C.lengthReplacement A D I n x y).comp
      (Cochain.ofHom (C.lengthInternalQuotient A D I n x y)) (add_zero 1) = 0 := by
  change (C.lengthReplacement A D I n x y).comp
    (Cochain.ofHom (C.lengthInclusion A D I n x y ≫ C.exactLengthProjection A D I n x y))
      (add_zero 1) = 0
  rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← lengthReplacement_inclusion]
  apply ComplexCoproduct.cochain_ext
  intro w
  rw [Cochain.comp_zero, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have h : Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w ≫
      C.lengthInclusion A D I n x y = C.inclusion A D I w.val x y :=
    ComplexCoproduct.ι_inclusion _ _ w
  rw [h, replacement_precomp]
  exact C.replaceRow_exactLength_projection A D I n x y w.val w.property

/-- 最終微分を持つ長さn以下のpathから、固定長nの内部複体へのchain map。 -/
def lengthQuotient (n : ℕ) (x y : D) :
    C.lengthHom A D I n x y ⟶ C.exactLengthHom A D I n x y :=
  perturbSourceMap (C.lengthInternalHom A D I n x y) (C.exactLengthHom A D I n x y)
    (C.lengthReplacement A D I n x y) (C.lengthReplacement_closed A D I n x y)
    (C.lengthReplacement_square_zero A D I n x y)
    (Cochain.ofHom (C.lengthInternalQuotient A D I n x y)) (by
      rw [δ_ofHom, lengthReplacement_quotient_zero])

lemma lengthQuotient_f (n : ℕ) (x y : D) (i : ℤ) :
    (C.lengthQuotient A D I n x y).f i = (C.lengthInternalQuotient A D I n x y).f i := rfl

lemma exactLengthHom_kFlat (hD : localHomKFlat A D) (n : ℕ) (x y : D) :
    complexKFlat A (C.exactLengthHom A D I n x y) := by
  have : HasExactColimitsOfShape (Discrete (exactLengthSet I n)) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} (exactLengthSet I n)).symm)
  exact complexKFlat_colimit A
    (Discrete.functor fun w : exactLengthSet I n => C.term A D I w.val x y)
    (fun w => C.term_kFlat A D I hD w.as.val x y)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
