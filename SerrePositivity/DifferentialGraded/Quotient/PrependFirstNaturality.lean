module
public import SerrePositivity.DifferentialGraded.Quotient.PrependAssociativity
public import SerrePositivity.DifferentialGraded.Quotient.ErasureHead
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaces

/-! # 先頭Hom合成と最初のε消去の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma prependMap_eraseMiddle {S : Set D} (c : S) (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D (c :: w) x y z)).comp
      (eraseMiddle A (homObject A D x c.val) (term A D w c.val z)) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y)
      (homObject A D y c.val ⊗ (epsilonComplex A ⊗ term A D w c.val z))
      (homObject A D y c.val ⊗ term A D w c.val z)).f 1
      (eraseMiddle A (homObject A D y c.val) (term A D w c.val z))).comp
      (Cochain.ofHom ((α_ (homObject A D x y) (homObject A D y c.val)
        (term A D w c.val z)).inv ≫ eComp (Complex A) x y c.val ▷ term A D w c.val z))
      (add_zero 1) := by
  simpa only [prependMap, tensorHom_id] using
    tensorJoin_eraseMiddle A (homObject A D x y) (homObject A D y c.val)
      (homObject A D x c.val) (term A D w c.val z) (eComp (Complex A) x y c.val)

/-- prependMapは最初のεを消す操作とも可換する。 -/
lemma prependMap_eraseFirst {S : Set D} (c : S) (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D (c :: w) x y z)).comp
      (eraseFirst A D c w x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D (c :: w) y z)
      (term A D w y z)).f 1 (eraseFirst A D c w y z)).comp
      (Cochain.ofHom (prependMap A D w x y z)) (add_zero 1) := by
  have hc : (α_ (homObject A D x y) (homObject A D y c.val) (term A D w c.val z)).inv ≫
      (eComp (Complex A) x y c.val ▷ term A D w c.val z) ≫ prependMap A D w x c.val z =
      (homObject A D x y) ◁ prependMap A D w y c.val z ≫ prependMap A D w x y z := by
    rw [prependMap_assoc, Iso.inv_hom_id_assoc]
  rw [eraseFirst, eraseFirst, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    prependMap_eraseMiddle, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  let M : Cochain (homObject A D x y ⊗ term A D (c :: w) y z)
      (homObject A D x y ⊗ (homObject A D y c.val ⊗ term A D w c.val z)) 1 :=
    (tensorLeftHom (homObject A D x y) (term A D (c :: w) y z)
      (homObject A D y c.val ⊗ term A D w c.val z)).f 1
        (eraseMiddle A (homObject A D y c.val) (term A D w c.val z))
  change M.comp (Cochain.ofHom _) (add_zero 1) = M.comp (Cochain.ofHom _) (add_zero 1)
  exact congrArg (fun f : homObject A D x y ⊗
      (homObject A D y c.val ⊗ term A D w c.val z) ⟶ term A D w x z =>
    M.comp (Cochain.ofHom f) (add_zero 1)) hc

end SerrePositivity.DifferentialGraded.DGQuotient
