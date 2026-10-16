module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaces

/-! # 各有限pathから全path直和へのε消去項

長さrのpathについてr個の消去cochainを足す。各項の終域を対応する短いpathの包含で揃える。
全直和の自己cochainとその二乗零は後続で構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- i番目の消去を、消去後のpathの全直和への包含と合成する。 -/
def eraseSummand {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    Cochain (term A D w x y) (internalHom A D S x y) 1 :=
  (eraseFace A D w i x y).comp
    (Cochain.ofHom (ι A D S x y (w.eraseIdx i))) (add_zero 1)

lemma eraseSummand_closed {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    δ 1 2 (eraseSummand A D w i x y) = 0 := by
  rw [eraseSummand, δ_comp_ofHom, eraseFace_closed]
  exact Cochain.zero_comp _ _

/-- 一つのpath上のε消去微分。和はその有限長にわたる。 -/
def eraseRow {S : Set D} (w : Word S) (x y : D) :
    Cochain (term A D w x y) (internalHom A D S x y) 1 :=
  ∑ i ∈ Finset.range w.length, eraseSummand A D w i x y

/-- 有限消去和も内部微分と反交換する。 -/
lemma eraseRow_closed {S : Set D} (w : Word S) (x y : D) :
    δ 1 2 (eraseRow A D w x y) = 0 := by
  change (δ_hom ℤ _ _ 1 2) (eraseRow A D w x y) = 0
  simp only [eraseRow, map_sum, δ_hom_apply, eraseSummand_closed,
    Finset.sum_const_zero]

@[simp] lemma eraseRow_nil (S : Set D) (x y : D) :
    eraseRow A D ([] : Word S) x y = 0 := by simp [eraseRow]

lemma eraseRow_singleton {S : Set D} (b : S) (x y : D) :
    eraseRow A D [b] x y = (eraseFirst A D b [] x y).comp
      (Cochain.ofHom (originalHom A D S x y)) (add_zero 1) := by
  simp only [eraseRow, List.length_cons, List.length_nil, zero_add, Finset.range_one,
    Finset.sum_singleton]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
