module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomUniversal

/-! # dg 関手 Hom end の実閉単位
概要：元の dg 関手の全対象の単位を、全次数自然性を保つ Hom end の単位にする。
方針：標的 dg 圏の左右単位律を使い、パラメータ普遍性で持ち上げる。
規約：閉零射上だけの自然性では代用しない。使われ方：dg 関手の豊穣圏構造の単位。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded

private lemma enrichedLeftUnit {A : Type u} [CommRing A] {E : Type w} [DGCategory A E]
    (x y : E) : eId (Complex A) x ▷ (x ⟶[Complex A] y) ≫ eComp (Complex A) x x y =
      (λ_ (x ⟶[Complex A] y)).hom := by
  apply (cancel_epi (λ_ (x ⟶[Complex A] y)).inv).mp
  exact (e_id_comp (Complex A) x y).trans (Iso.inv_hom_id _).symm

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] (F : DGFunctor A D E)

omit [Small.{u} D] in
/-- 元の dg 関手の全対象の単位は全次数自然。 -/
lemma dgFunctorIdentity_naturality (x y : D) :
    (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
      (F.map x y ⊗ₘ eId (Complex A) (F.obj y)) ≫ eComp (Complex A) _ _ _ =
    (eId (Complex A) (F.obj x) ⊗ₘ F.map x y) ≫ eComp (Complex A) _ _ _ := by
  rw [braiding_tensorUnit_left]
  rw [tensorHom_def, Category.assoc, Category.assoc,
    ← rightUnitor_inv_naturality_assoc, e_comp_id, Category.comp_id]
  rw [tensorHom_def', Category.assoc, enrichedLeftUnit, leftUnitor_naturality]

/-- 元の全対象の単位からなる、単位複体パラメータの全次数自然変換。 -/
def dgFunctorParamIdentity : DGFunctorParamTrans A D E (𝟙_ (Complex A)) F F where
  app x := eId (Complex A) (F.obj x)
  naturality := dgFunctorIdentity_naturality A D E F

/-- dg 関手 Hom end の元の全対象の単位を保持する閉単位。 -/
def dgFunctorIdentity : 𝟙_ (Complex A) ⟶ dgFunctorHom A D E F F :=
  (dgFunctorHomEquiv A D E _ F F).symm (dgFunctorParamIdentity A D E F)

/-- Hom end の閉単位は各対象で元の同じ dg 単位を回収する。 -/
@[reassoc (attr := simp)]
lemma dgFunctorIdentity_π (x : D) :
    dgFunctorIdentity A D E F ≫ dgFunctorHomπ A D E F F x = eId (Complex A) (F.obj x) :=
  dgFunctorHomEquiv_symm_π A D E _ F F (dgFunctorParamIdentity A D E F) x

end SerrePositivity.KST.SConstruction
