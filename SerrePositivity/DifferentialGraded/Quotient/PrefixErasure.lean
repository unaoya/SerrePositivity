module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureRowRecursion
public import SerrePositivity.DifferentialGraded.Quotient.ErasureHeadNaturality
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasure

/-! # 前方Homとεを追加する操作に対する全消去作用素の再帰式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 非空pathの全消去は、追加した先頭εの消去と、後方の全消去の和。 -/
lemma prefixPath_erasure {S : Set D} (b : S) (x y : D) :
    (Cochain.ofHom (prefixPath A D b x y)).comp (erasure A D S x y) (zero_add 1) =
    (eraseMiddle A (homObject A D x b.val) (internalHom A D S b.val y)).comp
      (Cochain.ofHom (internalPrepend A D S x b.val y)) (add_zero 1) +
    ((tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ internalHom A D S b.val y)
      (epsilonComplex A ⊗ internalHom A D S b.val y)).f 1
      ((tensorLeftHom (epsilonComplex A) (internalHom A D S b.val y)
        (internalHom A D S b.val y)).f 1 (erasure A D S b.val y))).comp
      (Cochain.ofHom (prefixPath A D b x y)) (add_zero 1) := by
  apply prefixPathCochain_ext A D b x y 1
  intro w
  have ht :
      (Cochain.ofHom ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))).comp
        ((tensorLeftHom (homObject A D x b.val)
          (epsilonComplex A ⊗ internalHom A D S b.val y)
          (epsilonComplex A ⊗ internalHom A D S b.val y)).f 1
          ((tensorLeftHom (epsilonComplex A) (internalHom A D S b.val y)
            (internalHom A D S b.val y)).f 1 (erasure A D S b.val y))) (zero_add 1) =
      (tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (epsilonComplex A ⊗ internalHom A D S b.val y)).f 1
        ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
          (internalHom A D S b.val y)).f 1 (eraseRow A D w b.val y)) := by
    rw [← tensorLeftHom_ofHom (homObject A D x b.val), ← tensorLeftHom_cochain_comp,
      ← tensorLeftHom_ofHom (epsilonComplex A), ← tensorLeftHom_cochain_comp, erasure_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    prefixPath_ι, erasure_precomp, Cochain.comp_add,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, eraseMiddle_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, internalPrepend_ι,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ht]
  exact eraseRow_cons A D b w x y

end SerrePositivity.DifferentialGraded.DGQuotient
