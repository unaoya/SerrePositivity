module
public import SerrePositivity.DifferentialGraded.Quotient.PrependFirstNaturality
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasureNaturality
public import SerrePositivity.DifferentialGraded.Quotient.InternalComposition
public import SerrePositivity.DifferentialGraded.Quotient.ErasureRows

/-! # 先頭Homの作用と全てのε消去項の自然性

空pathを左に置く合成について、ε消去のLeibniz則の基底式を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 先頭Hom合成は任意の位置のε消去と可換する。範囲外の位置も含む。 -/
lemma prependMap_eraseFace {S : Set D} (w : Word S) (i : ℕ) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (eraseFace A D w i x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D w y z)
      (term A D (w.eraseIdx i) y z)).f 1 (eraseFace A D w i y z)).comp
      (Cochain.ofHom (prependMap A D (w.eraseIdx i) x y z)) (add_zero 1) := by
  cases w with
  | nil => simp only [eraseFace_nil, map_zero, Cochain.comp_zero, Cochain.zero_comp]
  | cons c w =>
    cases i with
    | zero => exact prependMap_eraseFirst A D c w x y z
    | succ i => exact prependMap_eraseFace_succ A D c w i x y z

variable [Small.{u} D]

/-- 元のHomを全path直和の先頭へ合成する内部chain map。 -/
def internalPrepend (S : Set D) (x y z : D) :
    homObject A D x y ⊗ internalHom A D S y z ⟶ internalHom A D S x z :=
  (originalHom A D S x y ▷ internalHom A D S y z) ≫ internalComposition A D S x y z

lemma internalPrepend_ι (S : Set D) (x y z : D) (w : Word S) :
    ((homObject A D x y) ◁ ι A D S y z w) ≫ internalPrepend A D S x y z =
      prependMap A D w x y z ≫ ι A D S x z w := by
  rw [internalPrepend, ← Category.assoc, ← tensorHom_def', internalComposition_original_left]

/-- 一つのε消去項を全直和へ入れた後も先頭Hom作用と可換する。 -/
lemma prependMap_eraseSummand {S : Set D} (w : Word S) (i : ℕ) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (eraseSummand A D w i x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D w y z)
      (internalHom A D S y z)).f 1 (eraseSummand A D w i y z)).comp
      (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1) := by
  rw [eraseSummand, eraseSummand, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    prependMap_eraseFace, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, internalPrepend_ι]

/-- 一つのpath上の有限消去和は先頭Hom作用と可換する。 -/
lemma prependMap_eraseRow {S : Set D} (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (eraseRow A D w x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D w y z)
      (internalHom A D S y z)).f 1 (eraseRow A D w y z)).comp
      (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1) := by
  let L : Cochain (term A D w x z) (internalHom A D S x z) 1 →+
      Cochain (homObject A D x y ⊗ term A D w y z) (internalHom A D S x z) 1 :=
    { toFun := fun f => (Cochain.ofHom (prependMap A D w x y z)).comp f (zero_add 1)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun f g => Cochain.comp_add _ f g _ }
  let R : Cochain (term A D w y z) (internalHom A D S y z) 1 →+
      Cochain (homObject A D x y ⊗ term A D w y z) (internalHom A D S x z) 1 :=
    { toFun := fun f => ((tensorLeftHom (homObject A D x y) (term A D w y z)
        (internalHom A D S y z)).f 1 f).comp
        (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1)
      map_zero' := by rw [map_zero]; exact Cochain.zero_comp _ _
      map_add' := fun f g => by rw [map_add, Cochain.add_comp] }
  change L (eraseRow A D w x z) = R (eraseRow A D w y z)
  rw [eraseRow, eraseRow, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact prependMap_eraseSummand A D w i x y z

end SerrePositivity.DifferentialGraded.DGQuotient
