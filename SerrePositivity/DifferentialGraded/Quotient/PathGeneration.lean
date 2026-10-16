module
public import SerrePositivity.DifferentialGraded.Quotient.PrefixGeneration
public import SerrePositivity.DifferentialGraded.Quotient.Category
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonElement
public import SerrePositivity.DifferentialGraded.Quotient.CompositionEvaluation

/-! # 元のHomと指定εの反復合成によるpathの生成式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma prefixPath_generator {S : Set D} (b : S) (x y : D) (p q n : ℤ)
    (hn : p + ((-1) + q) = n) (a : (homObject A D x b.val).X p)
    (t : (internalHom A D S b.val y).X q) :
    (prefixPath A D b x y).f n
      (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
        p ((-1) + q) n hn (a ⊗ₜ[A]
          ιTensorObj (epsilonComplex A) (internalHom A D S b.val y) (-1) q ((-1) + q) rfl
            ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A (x := (⟨x⟩ : QuotientObject D S)) (y := ⟨b.val⟩) (z := ⟨y⟩)
      ((originalHomInclusion A D S x b.val).f p a)
      (forward A (x := (⟨b.val⟩ : QuotientObject D S)) (y := ⟨b.val⟩) (z := ⟨y⟩)
        (epsilonElement A D S b) t rfl) hn := by
  have h := congrArg (fun f : homObject A D x b.val ⊗
      (epsilonComplex A ⊗ internalHom A D S b.val y) ⟶ internalHom A D S x y =>
    f.f n (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
      p ((-1) + q) n hn (a ⊗ₜ[A]
        ιTensorObj (epsilonComplex A) (internalHom A D S b.val y) (-1) q ((-1) + q) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))))
    (prefixPath_generated A D b x y)
  simp only [internalPrepend, chain_comp_apply, whiskerLeft_apply, whiskerRight_apply] at h
  change _ = (quotientComposition A D S x b.val y).f n
    (ιTensorObj (quotientHom A D S x b.val) (quotientHom A D S b.val y) p ((-1) + q) n hn
      ((originalHomInclusion A D S x b.val).f p a ⊗ₜ[A]
        (quotientComposition A D S b.val b.val y).f ((-1) + q)
          (ιTensorObj (quotientHom A D S b.val b.val) (quotientHom A D S b.val y)
            (-1) q ((-1) + q) rfl (epsilonElement A D S b ⊗ₜ[A] t))))
  rw [quotientComposition_apply, quotientComposition_apply, originalHomInclusion_f]
  exact h.symm

lemma path_inclusion_generator {S : Set D} (b : S) (w : Word S) (x y : D) (p q n : ℤ)
    (hn : p + ((-1) + q) = n) (a : (homObject A D x b.val).X p)
    (t : (term A D w b.val y).X q) :
    (ι A D S x y (b :: w)).f n
      (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        p ((-1) + q) n hn (a ⊗ₜ[A]
          ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
            ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A (x := (⟨x⟩ : QuotientObject D S)) (y := ⟨b.val⟩) (z := ⟨y⟩)
      ((originalHomInclusion A D S x b.val).f p a)
      (forward A (x := (⟨b.val⟩ : QuotientObject D S)) (y := ⟨b.val⟩) (z := ⟨y⟩)
        (epsilonElement A D S b) ((ι A D S b.val y w).f q t) rfl) hn := by
  have h := congrArg (fun f : homObject A D x b.val ⊗
      (epsilonComplex A ⊗ term A D w b.val y) ⟶ internalHom A D S x y =>
    f.f n (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
      p ((-1) + q) n hn (a ⊗ₜ[A]
        ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))))
    (prefixPath_ι A D b x y w)
  simp only [chain_comp_apply, whiskerLeft_apply] at h
  exact h.symm.trans (prefixPath_generator A D b x y p q n hn a ((ι A D S b.val y w).f q t))

end SerrePositivity.DifferentialGraded.DGQuotient
