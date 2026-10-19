module

public import SerrePositivity.InfinityCategories.F1B.KanConeFunctorFiberEquivalence
public import SerrePositivity.InfinityCategories.F1B.KanNerveConeFamily
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：通常の錐と native な錐の族の比較を構成する。
方針：指数比較と固定図式上の fiber の同型を使う。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の局所極限の双方向比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalClosed
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：単体集合の同型による前合成を指数の同型にする。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
def kanPrecompositionIso {A B : SSet.{u}} (e : A ≅ B) (X : SSet.{u}) :
    (ihom B).obj X ≅ (ihom A).obj X where
  hom := (pre e.hom).app X
  inv := (pre e.inv).app X
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id]
    rfl
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id]
    rfl
/-- 概要：錐の拡張関手の nerve と join からの関手圏を同型にする。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
def kanNerveConeExtensionIso : nerve (WithInitial I ⥤ C) ≅
    (ihom (join (Δ[0] : SSet.{u}) (nerve I))).obj (nerve C) :=
  kanNerveFunctorCategoryIso (WithInitial I) C ≪≫
    kanPrecompositionIso (HomotopyLimits.initialJoinNerveIso I) (nerve C)
/-- 概要：錐の制限は指数比較と厳密に可換。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
lemma kanNerveConeRestriction_square : nerveMap (kanConeRestrictionFunctor (I := I) (C := C)) ≫
    (kanNerveFunctorCategoryIso I C).hom =
      (kanNerveConeExtensionIso (I := I) (C := C)).hom ≫ coneRestriction (nerve I) (nerve C) := by
  have hp : (pre (HomotopyLimits.initialJoinNerveIso I).hom).app (nerve C) ≫
      (pre (joinInr (Δ[0] : SSet.{u}) (nerve I))).app (nerve C) =
        (pre (nerveMap (WithInitial.incl : I ⥤ WithInitial I))).app (nerve C) := by
    rw [← NatTrans.comp_app, ← pre_map]
    have he := HomotopyLimits.joinInr_initialJoinNerveMap I
    change joinInr (Δ[0] : SSet.{u}) (nerve I) ≫
      (HomotopyLimits.initialJoinNerveIso I).hom = _ at he
    rw [he]
  change _ = (kanNerveFunctorCategoryIso (WithInitial I) C).hom ≫
    (pre (HomotopyLimits.initialJoinNerveIso I).hom).app (nerve C) ≫
      (pre (joinInr (Δ[0] : SSet.{u}) (nerve I))).app (nerve C)
  rw [hp]
  exact kanNerveFunctorCategoryIso_precomp (WithInitial.incl : I ⥤ WithInitial I)

end SerrePositivity.InfinityCategories.F1B
