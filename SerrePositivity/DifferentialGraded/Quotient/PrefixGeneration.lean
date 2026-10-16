module
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonAppend
public import SerrePositivity.DifferentialGraded.Quotient.InternalComposition
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasureRows
public import SerrePositivity.DifferentialGraded.Quotient.PathPrefix

/-! # 前方Hom・ε追加を元のHomとεの合成から復元する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma epsilon_internalComposition_ι {S : Set D} (b : S) (w : Word S) (y : D) :
    ((epsilonComplex A) ◁ ι A D S b.val y w) ≫
      (epsilon A D S b ▷ internalHom A D S b.val y) ≫ internalComposition A D S b.val b.val y =
    (epsilonTerm A D b ▷ term A D w b.val y) ≫ appendMap A D [b] w b.val b.val y ≫
      ι A D S b.val y (b :: w) := by
  rw [epsilon, comp_whiskerRight, Category.assoc, whisker_exchange_assoc,
    ← tensorHom_def'_assoc, internalComposition_ι]
  rfl

lemma prefixPath_generated {S : Set D} (b : S) (x y : D) :
    (homObject A D x b.val) ◁
      ((epsilon A D S b ▷ internalHom A D S b.val y) ≫ internalComposition A D S b.val b.val y) ≫
      internalPrepend A D S x b.val y = prefixPath A D b x y := by
  apply (prefixPathCofanIsColimit A D b x y).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ≫
      (homObject A D x b.val) ◁
        ((epsilon A D S b ▷ internalHom A D S b.val y) ≫
          internalComposition A D S b.val b.val y) ≫ internalPrepend A D S x b.val y =
    ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ≫ prefixPath A D b x y
  rw [prefixPath_ι, ← whiskerLeft_comp_assoc, epsilon_internalComposition_ι]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [internalPrepend_ι]
  have h := congrArg (fun f => f ≫ ι A D S x y (b :: w))
    (prependMap_epsilonTerm_append A D b w x y)
  simpa only [term_cons, whiskerLeft_comp, Category.assoc, Category.id_comp] using h

end SerrePositivity.DifferentialGraded.DGQuotient
