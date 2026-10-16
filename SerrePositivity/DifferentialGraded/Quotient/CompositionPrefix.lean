module
public import SerrePositivity.DifferentialGraded.Quotient.AppendRight
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproductExt

/-! # 全path合成と先頭Hom・εの追加の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma composition_prefix_left_ι {S : Set D} (b : S) (w : Word S) (x y z : D) :
    (((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ▷
    internalHom A D S y z) ≫ (prefixPath A D b x y ▷ internalHom A D S y z) ≫
      internalComposition A D S x y z = appendRight A D (b :: w) x y z := by
  rw [← comp_whiskerRight_assoc, prefixPath_ι, internalComposition_left_ι]

lemma composition_prefix_middle_ι {S : Set D} (b : S) (w : Word S) (y z : D) :
    (((epsilonComplex A) ◁ ι A D S b.val y w) ▷ internalHom A D S y z) ≫
    (α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
      (epsilonComplex A) ◁ internalComposition A D S b.val y z =
  (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
    (epsilonComplex A) ◁ appendRight A D w b.val y z := by
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, internalComposition_left_ι]

lemma composition_prefix_outer_ι {S : Set D} (b : S) (w : Word S) (x y z : D) :
    (((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ▷
    internalHom A D S y z) ≫
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
      (internalHom A D S y z)).hom ≫
    (homObject A D x b.val) ◁
      ((α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ internalComposition A D S b.val y z) =
  (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
    (internalHom A D S y z)).hom ≫
  (homObject A D x b.val) ◁
    ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
      (epsilonComplex A) ◁ appendRight A D w b.val y z) := by
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, composition_prefix_middle_ι]

/-- 各path上で先頭追加と全合成の二つの順序を比較する。 -/
lemma composition_prefix_restrict {S : Set D} (b : S) (w : Word S) (x y z : D) :
    (((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ▷
      internalHom A D S y z) ≫ (prefixPath A D b x y ▷ internalHom A D S y z) ≫
      internalComposition A D S x y z =
    (((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ▷
      internalHom A D S y z) ≫
      (α_ (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
        (internalHom A D S y z)).hom ≫ (homObject A D x b.val) ◁
        ((α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
          (epsilonComplex A) ◁ internalComposition A D S b.val y z) ≫ prefixPath A D b x z := by
  have hr := congrArg (fun f => f ≫ prefixPath A D b x z)
    (composition_prefix_outer_ι A D b w x y z)
  simp only [Category.assoc] at hr
  exact (composition_prefix_left_ι A D b w x y z).trans
      ((appendRight_cons A D b w x y z).trans hr.symm)

/-- 先頭Homとεを追加してから合成しても、後方を合成してから追加しても一致する。 -/
lemma internalComposition_prefixPath {S : Set D} (b : S) (x y z : D) :
    (prefixPath A D b x y ▷ internalHom A D S y z) ≫ internalComposition A D S x y z =
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
      (internalHom A D S y z)).hom ≫
    (homObject A D x b.val) ◁
      ((α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ internalComposition A D S b.val y z) ≫ prefixPath A D b x z := by
  apply tensorLeftTwoRightCoproduct_hom_ext (homObject A D x b.val) (epsilonComplex A)
    (internalHom A D S y z) (fun w : Word S => term A D w b.val y)
  intro w
  exact composition_prefix_restrict A D b w x y z

end SerrePositivity.DifferentialGraded.DGQuotient
