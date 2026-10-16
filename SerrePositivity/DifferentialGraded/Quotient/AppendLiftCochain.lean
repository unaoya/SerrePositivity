module
public import SerrePositivity.DifferentialGraded.Quotient.CompositionPrefix
public import SerrePositivity.DifferentialGraded.Quotient.ErasureRowRecursion
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochain

/-! # 連結の帰納ステップへ後方cochainを持ち上げる操作 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 前方Homとεを付け直し、後方の連結cochainを全pathへ戻す。 -/
def appendLiftCochain {S : Set D} (b : S) (w : Word S) (x y z : D) (p : ℤ)
    (f : Cochain (term A D w b.val y ⊗ internalHom A D S y z)
      (internalHom A D S b.val z) p) :
    Cochain (term A D (b :: w) x y ⊗ internalHom A D S y z) (internalHom A D S x z) p :=
  ((Cochain.ofHom ((α_ (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y) (internalHom A D S y z)).hom ≫
      (homObject A D x b.val) ◁
        (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom)).comp
    ((tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ (term A D w b.val y ⊗ internalHom A D S y z))
      (epsilonComplex A ⊗ internalHom A D S b.val z)).f p
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y ⊗ internalHom A D S y z)
        (internalHom A D S b.val z)).f p f)) (zero_add p)).comp
      (Cochain.ofHom (prefixPath A D b x z)) (add_zero p)

lemma appendLiftCochain_add {S : Set D} (b : S) (w : Word S) (x y z : D) (p : ℤ)
    (f g : Cochain (term A D w b.val y ⊗ internalHom A D S y z)
      (internalHom A D S b.val z) p) :
    appendLiftCochain A D b w x y z p (f + g) =
      appendLiftCochain A D b w x y z p f + appendLiftCochain A D b w x y z p g := by
  simp only [appendLiftCochain, map_add]
  rw [Cochain.comp_add _ _ _ (zero_add p)]
  exact Cochain.add_comp _ _ _ (add_zero p)

/-- 左語の後方cochainによる項は、短い語での項の持ち上げに等しい。 -/
lemma appendLiftCochain_left {S : Set D} (b : S) (w : Word S) (x y z : D) (p : ℤ)
    (f : Cochain (term A D w b.val y) (internalHom A D S b.val y) p) :
    ((tensorRightHom (internalHom A D S y z) (term A D (b :: w) x y)
      (internalHom A D S x y)).f p (prefixTailCochain A D b w x y p f)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero p) =
    appendLiftCochain A D b w x y z p
      (((tensorRightHom (internalHom A D S y z) (term A D w b.val y)
        (internalHom A D S b.val y)).f p f).comp
          (Cochain.ofHom (internalComposition A D S b.val y z)) (add_zero p)) := by
  rw [prefixTailCochain, tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_prefixPath]
  rw [appendLiftCochain, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  have h := prefixTensor_cochain_middle (homObject A D x b.val) (epsilonComplex A)
    (term A D w b.val y) (internalHom A D S b.val y) (internalHom A D S y z) p f
  simp only [term_cons, whiskerLeft_comp, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain] at h ⊢
  rw [h]

/-- 右側cochainによる項も短い語での項の持ち上げに等しい。 -/
lemma appendLiftCochain_right {S : Set D} (b : S) (w : Word S) (x y z : D) (p : ℤ)
    (f : Cochain (internalHom A D S y z) (internalHom A D S y z) p) :
    ((tensorLeftHom (term A D (b :: w) x y) (internalHom A D S y z)
      (internalHom A D S y z)).f p f).comp
      (Cochain.ofHom (appendRight A D (b :: w) x y z)) (add_zero p) =
    appendLiftCochain A D b w x y z p
      (((tensorLeftHom (term A D w b.val y) (internalHom A D S y z)
        (internalHom A D S y z)).f p f).comp
          (Cochain.ofHom (appendRight A D w b.val y z)) (add_zero p)) := by
  rw [appendRight_cons, appendLiftCochain,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  have h := prefixTensor_cochain_right (homObject A D x b.val) (epsilonComplex A)
    (term A D w b.val y) (internalHom A D S y z) (internalHom A D S y z) p f
  simp only [term_cons, whiskerLeft_comp, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain] at h ⊢
  rw [h]

end SerrePositivity.DifferentialGraded.DGQuotient
