module
public import SerrePositivity.DifferentialGraded.Quotient.Associativity
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # 明示的path商のMathlib豊穣dg圏 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の対象と一対一に対応する商の対象。元のdg構造とのinstance衝突を避ける。 -/
structure QuotientObject (D : Type v) (S : Set D) where
  val : D

/-- 商は対象を変更しない。 -/
def quotientObjectEquiv (S : Set D) : D ≃ QuotientObject D S where
  toFun x := ⟨x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- 最終Hom・単位・合成・三つの法則から得られる主豊穣dg構造。 -/
instance quotientDGCategory (S : Set D) : DGCategory A (QuotientObject D S) :=
  ofHomObjects A (QuotientObject D S)
    (fun x y => quotientHom A D S x.val y.val)
    (fun x => quotientIdentity A D S x.val)
    (fun x y z => quotientComposition A D S x.val y.val z.val)
    (fun x y => quotientComposition_left_unit A D S x.val y.val)
    (fun x y => quotientComposition_right_unit A D S x.val y.val)
    (fun w x y z => by
      rw [quotientComposition_assoc, Iso.inv_hom_id_assoc])

/-- 元のHomの空path包含によるdg関手。 -/
def inclusion (S : Set D) : DGFunctor A D (QuotientObject D S) where
  obj x := ⟨x⟩
  map x y := originalHomInclusion A D S x y
  map_id _x := rfl
  map_comp x y z := (quotientComposition_original A D S x y z).symm

/-- 豊穣合成の成分と通常順dg合成のKoszul比較。 -/
lemma quotientComposition_eq_signed_compose (S : Set D) (x y z : D)
    (p q n : ℤ) (hn : p + q = n)
    (f : (quotientHom A D S x y).X p) (g : (quotientHom A D S y z).X q) :
    (quotientComposition A D S x y z).f n
      (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) p q n hn (f ⊗ₜ[A] g)) =
    (p * q).negOnePow • compose A (x := (⟨x⟩ : QuotientObject D S))
      (y := (⟨y⟩ : QuotientObject D S)) (z := (⟨z⟩ : QuotientObject D S)) g f hn :=
  forward_eq_signed_compose A (D := QuotientObject D S)
    (x := ⟨x⟩) (y := ⟨y⟩) (z := ⟨z⟩) f g hn

end SerrePositivity.DifferentialGraded.DGQuotient
