module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionCoendCoherence
public import SerrePositivity.DifferentialGraded.Quotient.Paths

/-! # 同じ有限語を添字とする path 項の係数変更

空語も含めて Word S = List S を変更しない。ここでは内部微分を扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

/-- 同じ有限語の各 Hom と ε に係数変更を施す。 -/
def termBaseChangeIso {S : Set D} : ∀ (w : Word S) (x y : D),
    (extension φ).obj (term A D w x y) ≅ term A' (DGBaseChange φ D) w x y
  | [], _, _ => Iso.refl _
  | b :: w, x, y =>
    tensorIso φ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y) ≪≫
      cochainTensorIso (Iso.refl _)
        (tensorIso φ (epsilonComplex A) (term A D w b.val y) ≪≫
          cochainTensorIso (sphereIso φ (-1)) (termBaseChangeIso w b.val y))

@[simp]
lemma termBaseChangeIso_nil (S : Set D) (x y : D) :
    termBaseChangeIso φ D ([] : Word S) x y = Iso.refl _ := rfl

lemma termBaseChangeIso_cons_hom {S : Set D} (b : S) (w : Word S) (x y : D) :
    (termBaseChangeIso φ D (b :: w) x y).hom =
      (tensorIso φ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)).hom ≫
        (extension φ).obj (homObject A D x b.val) ◁
          ((tensorIso φ (epsilonComplex A) (term A D w b.val y)).hom ≫
            ((sphereIso φ (-1)).hom ⊗ₘ (termBaseChangeIso φ D w b.val y).hom)) := by
  simp only [termBaseChangeIso, Iso.trans_hom, cochainTensorIso,
    MonoidalCategory.tensorIso_hom, Iso.refl_hom, id_tensorHom]

variable [Small.{u} D]

/-- path の直和は同じ Word S を添字とする直和へ移る。 -/
def internalHomBaseChangeIso (S : Set D) (x y : D) :
    (extension φ).obj (internalHom A D S x y) ≅
      internalHom A' (DGBaseChange φ D) S x y :=
  coproductIso φ (fun w : Word S => term A D w x y) ≪≫
    Sigma.mapIso (fun w : Word S => termBaseChangeIso φ D w x y)

@[reassoc (attr := simp)]
lemma map_ι_internalHomBaseChangeIso (S : Set D) (x y : D) (w : Word S) :
    (extension φ).map (ι A D S x y w) ≫ (internalHomBaseChangeIso φ D S x y).hom =
      (termBaseChangeIso φ D w x y).hom ≫ ι A' (DGBaseChange φ D) S x y w := by
  simp only [internalHomBaseChangeIso, Iso.trans_hom]
  rw [show ι A D S x y w = Sigma.ι (fun w : Word S => term A D w x y) w from rfl,
    map_ι_coproductIso_assoc, Sigma.ι_mapIso_hom]
  rfl

@[reassoc (attr := simp)]
lemma map_originalHom_internalHomBaseChangeIso (S : Set D) (x y : D) :
    (extension φ).map (originalHom A D S x y) ≫ (internalHomBaseChangeIso φ D S x y).hom =
      originalHom A' (DGBaseChange φ D) S x y := by
  have h := map_ι_internalHomBaseChangeIso φ D S x y []
  simp only [termBaseChangeIso_nil, Iso.refl_hom, Category.id_comp] at h
  convert h using 1 <;> rfl

end SerrePositivity.DifferentialGraded.DGQuotient
