module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoproductInternalHom
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConstantDiagram

/-!
概要：直和の内部 Hom と二つの内部 Hom の積の厳密な同型。
方針：二つの制限を組にし、uncurry した射の貼り合わせを逆にする。
規約：定値図式の二つの成分も厳密に一致する。
使われ方：二項対角関手の right cofinality。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：直和からの関手は二つの関手の組と厳密に同じ。
方針：制限と貼り合わせの往復を各脚で計算する。
規約：三つの形状は任意。使われ方：対角関手の積表示。 -/
def coproductFunctorIso (A B X : SSet.{u}) :
    (ihom (A ⨿ B)).obj X ≅ (ihom A).obj X ⊗ (ihom B).obj X where
  hom := lift ((pre (coprod.inl : A ⟶ A ⨿ B)).app X)
    ((pre (coprod.inr : B ⟶ A ⨿ B)).app X)
  inv := coproductFunctorGlue (fst _ _) (snd _ _)
  hom_inv_id := by
    apply coproductFunctor_hom_ext
    · rw [Category.assoc, coproductFunctorGlue_inl, lift_fst, Category.id_comp]
    · rw [Category.assoc, coproductFunctorGlue_inr, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, coproductFunctorGlue_inl, Category.id_comp]
    · rw [Category.assoc, lift_snd, coproductFunctorGlue_inr, Category.id_comp]

/-- 概要：定値図式の制限は元の形状の定値図式。
方針：uncurry して第二射影を計算する。
規約：任意の形状射。使われ方：定値図式の積表示の両成分。 -/
lemma constantDiagram_pre {A B X : SSet.{u}} (f : A ⟶ B) :
    constantDiagram B X ≫ (pre f).app X = constantDiagram A X := by
  apply uncurry_injective
  rw [uncurry_pre_app, constantDiagram, uncurry_curry, constantDiagram, uncurry_curry]
  exact whiskerRight_snd f X

/-- 概要：直和の定値図式は二つの定値図式の対角の組になる。
方針：同型の二射影と定値図式の制限を使う。
規約：厳密な等式。使われ方：二項対角の cofinality の輸送。 -/
lemma constantDiagram_coproductFunctorIso (A B X : SSet.{u}) :
    constantDiagram (A ⨿ B) X ≫ (coproductFunctorIso A B X).hom =
      lift (constantDiagram A X) (constantDiagram B X) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [coproductFunctorIso, Category.assoc, lift_fst, lift_fst, constantDiagram_pre]
  · rw [coproductFunctorIso, Category.assoc, lift_snd, lift_snd, constantDiagram_pre]

end SerrePositivity.InfinityCategories.F2
