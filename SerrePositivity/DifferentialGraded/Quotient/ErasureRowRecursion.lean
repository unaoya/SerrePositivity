module
public import SerrePositivity.DifferentialGraded.Quotient.PathPrefix
public import SerrePositivity.DifferentialGraded.Quotient.ErasureRows
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaceEquations
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero

/-! # 非空pathのε消去和を先頭と後方へ分ける再帰式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 後方cochainを先頭Homとεでtensorし、先頭を追加したpath直和へ送る。 -/
def prefixTailCochain {S : Set D} (b : S) (w : Word S) (x y : D) (p : ℤ)
    (f : Cochain (term A D w b.val y) (internalHom A D S b.val y) p) :
    Cochain (term A D (b :: w) x y) (internalHom A D S x y) p :=
  ((tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
    (epsilonComplex A ⊗ internalHom A D S b.val y)).f p
    ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
      (internalHom A D S b.val y)).f p f)).comp
    (Cochain.ofHom (prefixPath A D b x y)) (add_zero p)

/-- 後方の消去項は短いpathの消去項を二重tensorし、先頭を追加したもの。 -/
lemma eraseSummand_cons_succ {S : Set D} (b : S) (w : Word S) (i : ℕ) (x y : D) :
    eraseSummand A D (b :: w) (i + 1) x y =
    prefixTailCochain A D b w x y 1 (eraseSummand A D w i b.val y) := by
  rw [prefixTailCochain, eraseSummand, eraseSummand, eraseFace_cons_succ,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, prefixPath_ι]
  rfl

/-- 非空pathの消去和は、先頭εの消去と、先頭を保持する後方消去和の和である。 -/
lemma eraseRow_cons {S : Set D} (b : S) (w : Word S) (x y : D) :
    eraseRow A D (b :: w) x y =
    (eraseFirst A D b w x y).comp (Cochain.ofHom (ι A D S x y w)) (add_zero 1) +
    prefixTailCochain A D b w x y 1 (eraseRow A D w b.val y) := by
  let R : Cochain (term A D w b.val y) (internalHom A D S b.val y) 1 →+
      Cochain (term A D (b :: w) x y) (internalHom A D S x y) 1 :=
    { toFun := prefixTailCochain A D b w x y 1
      map_zero' := by simp only [prefixTailCochain, map_zero, Cochain.zero_comp]
      map_add' := fun f g => by
        simp only [prefixTailCochain, map_add]
        exact Cochain.add_comp _ _ _ (add_zero 1) }
  have hs : ∑ i ∈ Finset.range w.length, eraseSummand A D (b :: w) (i + 1) x y =
      R (eraseRow A D w b.val y) := by
    rw [eraseRow, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact eraseSummand_cons_succ A D b w i x y
  have hz : eraseSummand A D (b :: w) 0 x y =
      (eraseFirst A D b w x y).comp (Cochain.ofHom (ι A D S x y w)) (add_zero 1) := rfl
  rw [eraseRow, List.length_cons, Finset.sum_range_succ', hs, hz]
  exact add_comm _ _

end SerrePositivity.DifferentialGraded.DGQuotient
