module
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasureRows
public import SerrePositivity.DifferentialGraded.Quotient.PathPrefix

/-! # 左pathを固定した全path直和への連結 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左の有限pathを固定し、右の全pathへ連結する内部chain map。 -/
def appendRight {S : Set D} (w : Word S) (x y z : D) :
    term A D w x y ⊗ internalHom A D S y z ⟶ internalHom A D S x z :=
  tensorCoproductRightDesc (term A D w x y) (fun v : Word S => term A D v y z)
    (internalHom A D S x z) (fun v => appendMap A D w v x y z ≫ ι A D S x z (w ++ v))

lemma appendRight_ι {S : Set D} (w v : Word S) (x y z : D) :
    (term A D w x y ◁ ι A D S y z v) ≫ appendRight A D w x y z =
      appendMap A D w v x y z ≫ ι A D S x z (w ++ v) :=
  tensorCoproductRightDesc_ι _ _ _ _ v

lemma internalComposition_left_ι (S : Set D) (w : Word S) (x y z : D) :
    (ι A D S x y w ▷ internalHom A D S y z) ≫ internalComposition A D S x y z =
      appendRight A D w x y z := tensorCoproductDesc_left _ _ _ _ w

/-- 左pathが空なら先頭Hom作用に戻る。 -/
lemma appendRight_nil (S : Set D) (x y z : D) :
    appendRight A D ([] : Word S) x y z = internalPrepend A D S x y z := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y)
    (fun v : Word S => term A D v y z)).hom_ext
  rintro ⟨v⟩
  change (homObject A D x y ◁ ι A D S y z v) ≫ appendRight A D [] x y z =
    (homObject A D x y ◁ ι A D S y z v) ≫ internalPrepend A D S x y z
  exact (appendRight_ι A D [] v x y z).trans (internalPrepend_ι A D S x y z v).symm

/-- 非空の左pathの連結は、短いpathの連結に前方Homとεを戻したもの。 -/
lemma appendRight_cons {S : Set D} (b : S) (w : Word S) (x y z : D) :
    appendRight A D (b :: w) x y z =
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
      (internalHom A D S y z)).hom ≫
    (homObject A D x b.val) ◁
      ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y z) ≫ prefixPath A D b x z := by
  apply (tensorLeftCoproductIsColimit (term A D (b :: w) x y)
    (fun v : Word S => term A D v y z)).hom_ext
  rintro ⟨v⟩
  have hm : ((epsilonComplex A ⊗ term A D w b.val y) ◁ ι A D S y z v) ≫
      (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y z =
    (α_ (epsilonComplex A) (term A D w b.val y) (term A D v y z)).hom ≫
      (epsilonComplex A) ◁ appendMap A D w v b.val y z ≫
        (epsilonComplex A) ◁ ι A D S b.val z (w ++ v) := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, appendRight_ι, whiskerLeft_comp]
  have ht : ((homObject A D x b.val ⊗ (epsilonComplex A ⊗ term A D w b.val y)) ◁
      ι A D S y z v) ≫
      (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (internalHom A D S y z)).hom ≫
      (homObject A D x b.val) ◁
        ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
          (epsilonComplex A) ◁ appendRight A D w b.val y z) =
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
      (term A D v y z)).hom ≫
      (homObject A D x b.val) ◁ (α_ (epsilonComplex A) (term A D w b.val y)
        (term A D v y z)).hom ≫
      (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ appendMap A D w v b.val y z) ≫
      (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val z (w ++ v)) := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, hm]
    simp only [whiskerLeft_comp]
  have h := congrArg (fun f => f ≫ prefixPath A D b x z) ht
  simp only [Category.assoc, prefixPath_ι] at h
  change (term A D (b :: w) x y ◁ ι A D S y z v) ≫ appendRight A D (b :: w) x y z = _
  rw [appendRight_ι]
  simpa only [Cofan.mk_ι_app, term_cons, appendMap, ι, List.cons_append,
    whiskerLeft_comp, Category.assoc] using h.symm

end SerrePositivity.DifferentialGraded.DGQuotient
