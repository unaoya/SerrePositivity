module
public import SerrePositivity.DifferentialGraded.Quotient.DoubleFaces
public import SerrePositivity.DifferentialGraded.Quotient.ErasureOperator
public import SerrePositivity.DifferentialGraded.Quotient.ErasureCancellation

/-! # 二重消去を全path直和へ入れた項の反交換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 終域の語付きcochainを全path直和へ入れる。 -/
def includeDoubleFace {S : Set D} {w : Word S} {x y : D} :
    DoubleFace A D w x y → Cochain (term A D w x y) (internalHom A D S x y) 2
  | ⟨z, f⟩ => f.comp (Cochain.ofHom (ι A D S x y z)) (add_zero 2)

lemma includeDoubleFace_negate {S : Set D} {w : Word S} {x y : D}
    (f : DoubleFace A D w x y) :
    includeDoubleFace A D (negateDoubleFace A D f) = -includeDoubleFace A D f := by
  rcases f with ⟨z, f⟩
  simp only [includeDoubleFace, negateDoubleFace, Cochain.neg_comp]

/-- 二重消去をその終域のpath包含と合成した項。 -/
def erasurePair {S : Set D} (w : Word S) (i j : ℕ) (x y : D) :
    Cochain (term A D w x y) (internalHom A D S x y) 2 :=
  includeDoubleFace A D (doubleFace A D w i j x y)

lemma erasurePair_swap_of_le {S : Set D} (w : Word S) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    erasurePair A D w i j x y = -erasurePair A D w (j + 1) i x y := by
  exact (congrArg (includeDoubleFace A D) (doubleFace_swap_of_le A D w i j hij x y)).trans
    (includeDoubleFace_negate A D _)

/-- 有限和相殺の対合が、実際の二重消去項を負にする。 -/
lemma erasurePair_swap {S : Set D} (w : Word S) (i j : ℕ) (x y : D) :
    erasurePair A D w i j x y =
      -erasurePair A D w (swapErasure (i, j)).1 (swapErasure (i, j)).2 x y := by
  by_cases hij : j < i
  · have h := erasurePair_swap_of_le A D w j (i - 1) (by omega) x y
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at h
    simp only [swapErasure, ite_eq_left hij]
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  · simpa only [swapErasure, Prod.fst, Prod.snd, ite_eq_right hij] using
      erasurePair_swap_of_le A D w i j (by omega) x y

lemma erasurePair_double_sum_zero {S : Set D} (w : Word S) (x y : D) :
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range (w.length - 1),
      erasurePair A D w i j x y = 0 :=
  erasure_double_sum_cancel w.length (fun i j => erasurePair A D w i j x y)
    (fun i _ j _ => erasurePair_swap A D w i j x y)

end SerrePositivity.DifferentialGraded.DGQuotient
