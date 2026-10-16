module
public import SerrePositivity.DifferentialGraded.Quotient.DoubleFaceSum
public import SerrePositivity.DifferentialGraded.Quotient.PathCochainExt

/-! # 全path直和のε消去作用素の二乗零 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 作用素の二乗を各pathへ制限すると、全ての二重消去項の有限二重和になる。 -/
lemma erasure_square_precomp_double_sum (S : Set D) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp
      ((erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega))
      (zero_add 2) =
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range (w.length - 1),
      erasurePair A D w i j x y := by
  rw [erasure_square_precomp]
  apply Finset.sum_congr rfl
  intro i hi
  let R : Cochain (term A D (w.eraseIdx i) x y) (internalHom A D S x y) 1 →+
      Cochain (term A D w x y) (internalHom A D S x y) 2 :=
    { toFun := fun f => (eraseFace A D w i x y).comp f (by omega)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun f g => Cochain.comp_add _ f g _ }
  change R (eraseRow A D (w.eraseIdx i) x y) = _
  rw [eraseRow, map_sum, List.length_eraseIdx_of_lt (Finset.mem_range.mp hi)]
  apply Finset.sum_congr rfl
  intro j _
  change (eraseFace A D w i x y).comp
      ((eraseFace A D (w.eraseIdx i) j x y).comp
        (Cochain.ofHom (ι A D S x y ((w.eraseIdx i).eraseIdx j))) (add_zero 1))
      (show (1 : ℤ) + 1 = 2 by omega) =
    ((eraseFace A D w i x y).comp (eraseFace A D (w.eraseIdx i) j x y)
      (show (1 : ℤ) + 1 = 2 by omega)).comp
        (Cochain.ofHom (ι A D S x y ((w.eraseIdx i).eraseIdx j))) (add_zero 2)
  exact (Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ _).symm

/-- 全path直和のε消去作用素は二乗零である。 -/
lemma erasure_square_zero (S : Set D) (x y : D) :
    (erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega) = 0 := by
  apply pathCochain_ext A D S x y 2
  intro w
  rw [erasure_square_precomp_double_sum, erasurePair_double_sum_zero, Cochain.comp_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
