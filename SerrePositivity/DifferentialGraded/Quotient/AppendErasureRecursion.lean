module
public import SerrePositivity.DifferentialGraded.Quotient.AppendErasureHead
public import SerrePositivity.DifferentialGraded.Quotient.AppendLiftCochain
public import SerrePositivity.DifferentialGraded.Quotient.PrefixErasure

/-! # 非空左pathの連結後の消去作用素の再帰式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 非空左pathの連結後の消去は、先頭ε消去と短いpathの消去の持ち上げの和。 -/
lemma appendRight_erasure_cons {S : Set D} (b : S) (w : Word S) (x y z : D) :
    (Cochain.ofHom (appendRight A D (b :: w) x y z)).comp (erasure A D S x z)
      (zero_add 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D (b :: w) x y) (term A D w x y)).f 1
      (eraseFirst A D b w x y)).comp (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) +
    appendLiftCochain A D b w x y z 1
      ((Cochain.ofHom (appendRight A D w b.val y z)).comp (erasure A D S b.val z)
        (zero_add 1)) := by
  let sigma := (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
    (internalHom A D S y z)).hom ≫ (homObject A D x b.val) ◁
      (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom
  let tau := (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ appendRight A D w b.val y z)
  have hc : appendRight A D (b :: w) x y z =
      (sigma ≫ tau) ≫ prefixPath A D b x z := by
    rw [appendRight_cons]
    simp only [sigma, tau, whiskerLeft_comp, Category.assoc]
  have hh : ((Cochain.ofHom (sigma ≫ tau)).comp
      (eraseMiddle A (homObject A D x b.val) (internalHom A D S b.val z)) (zero_add 1)).comp
      (Cochain.ofHom (internalPrepend A D S x b.val z)) (add_zero 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D (b :: w) x y) (term A D w x y)).f 1
      (eraseFirst A D b w x y)).comp (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) := by
    simpa only [sigma, tau, Category.assoc] using appendRight_eraseFirst A D b w x y z
  rw [hc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, prefixPath_erasure]
  rw [Cochain.comp_add _ _ _ (zero_add 1),
    ← Cochain.comp_assoc_of_first_is_zero_cochain, hh]
  congr 1
  simp only [appendLiftCochain, sigma, tau, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    term_cons, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.DifferentialGraded.DGQuotient
