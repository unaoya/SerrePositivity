module
public import SerrePositivity.DifferentialGraded.Quotient.PathComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # 内部微分を持つ全path直和の合成

有限pathの連結を二つの直和のtensorへ延長する。この段階のchain mapは内部微分に関するもので、
最終微分との両立はε消去のLeibniz則から後続で証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 内部微分に関する全有限pathの合成。 -/
def internalComposition (S : Set D) (x y z : D) :
    internalHom A D S x y ⊗ internalHom A D S y z ⟶ internalHom A D S x z :=
  tensorCoproductDesc (fun w : Word S => term A D w x y)
    (fun v : Word S => term A D v y z) (internalHom A D S x z)
    (fun w v => appendMap A D w v x y z ≫ ι A D S x z (w ++ v))

lemma internalComposition_ι (S : Set D) (x y z : D) (w v : Word S) :
    (ι A D S x y w ⊗ₘ ι A D S y z v) ≫ internalComposition A D S x y z =
      appendMap A D w v x y z ≫ ι A D S x z (w ++ v) :=
  tensorCoproductDesc_ι _ _ _ _ w v

/-- 内部path Hom二つのtensorからのchain mapは、各二つのpath上で決まる。 -/
lemma internalComposition_hom_ext (S : Set D) (x y z : D) {T : Complex A}
    (f g : internalHom A D S x y ⊗ internalHom A D S y z ⟶ T)
    (h : ∀ w v : Word S, (ι A D S x y w ⊗ₘ ι A D S y z v) ≫ f =
      (ι A D S x y w ⊗ₘ ι A D S y z v) ≫ g) : f = g :=
  tensorCoproduct_hom_ext _ _ f g h

lemma internalComposition_original_left (S : Set D) (x y z : D) (w : Word S) :
    (originalHom A D S x y ⊗ₘ ι A D S y z w) ≫ internalComposition A D S x y z =
      prependMap A D w x y z ≫ ι A D S x z w :=
  internalComposition_ι A D S x y z [] w

lemma internalComposition_original_original (S : Set D) (x y z : D) :
    (originalHom A D S x y ⊗ₘ originalHom A D S y z) ≫ internalComposition A D S x y z =
      eComp (Complex A) x y z ≫ originalHom A D S x z :=
  internalComposition_ι A D S x y z [] []

/-- 純tensor上で、二つのpathの斉次成分は連結後のpath包含へ送られる。 -/
lemma internalComposition_apply (S : Set D) (x y z : D) (w v : Word S)
    (p q n : ℤ) (hn : p + q = n) (f : (term A D w x y).X p)
    (g : (term A D v y z).X q) :
    (internalComposition A D S x y z).f n
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn
        ((ι A D S x y w).f p f ⊗ₜ[A] (ι A D S y z v).f q g)) =
    (ι A D S x z (w ++ v)).f n ((appendMap A D w v x y z).f n
      (ιTensorObj (term A D w x y) (term A D v y z) p q n hn (f ⊗ₜ[A] g))) := by
  have h := congrArg (fun F : term A D w x y ⊗ term A D v y z ⟶ internalHom A D S x z =>
    F.f n (ιTensorObj (term A D w x y) (term A D v y z) p q n hn (f ⊗ₜ[A] g)))
    (internalComposition_ι A D S x y z w v)
  change (internalComposition A D S x y z).f n
    ((ι A D S x y w ⊗ₘ ι A D S y z v).f n
      (ιTensorObj (term A D w x y) (term A D v y z) p q n hn (f ⊗ₜ[A] g))) = _ at h
  rw [tensorMap_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
