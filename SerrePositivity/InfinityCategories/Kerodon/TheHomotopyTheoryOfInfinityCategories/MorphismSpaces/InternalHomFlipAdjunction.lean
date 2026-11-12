module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
概要：標的を固定した反変内部 Hom の自己随伴。
方針：直積の対称性で二変数の curry を入れ替える。
規約：任意の単体集合 X を扱い、quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の前合成の境界持ち上げとセルによる閉包。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：標的を固定した二変数の内部 Hom の射の同値。
方針：uncurry 後に直積の二因子を交換して curry する。
規約：二つの始域は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の持ち上げ問題の交換。 -/
noncomputable def internalHomFlipHomEquiv (A B X : SSet.{u}) :
    (A ⟶ (ihom B).obj X) ≃ (B ⟶ (ihom A).obj X) where
  toFun f := curry ((β_ A B).hom ≫ uncurry f)
  invFun f := curry ((β_ B A).hom ≫ uncurry f)
  left_inv f := by simp
  right_inv f := by simp

/-- 概要：内部 Hom の射の交換は第一の始域の前合成を内部 Hom の制限に変える。
方針：uncurry の自然性と braiding の自然性を使う。
規約：前合成する射は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の反変随伴の自然性。 -/
lemma internalHomFlipHomEquiv_pre {A A' B X : SSet.{u}}
    (i : A' ⟶ A) (f : A ⟶ (ihom B).obj X) :
    internalHomFlipHomEquiv A' B X (i ≫ f) =
      internalHomFlipHomEquiv A B X f ≫ (pre i).app X := by
  change curry ((β_ A' B).hom ≫ uncurry (i ≫ f)) =
    curry ((β_ A B).hom ≫ uncurry f) ≫ (pre i).app X
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry, uncurry_natural_left]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc]

/-- 概要：内部 Hom の制限の後合成は交換後の始域の前合成になる。
方針：uncurry の制限の式と braiding の自然性を使う。
規約：制限する射は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の反変随伴の自然性。 -/
lemma internalHomFlipHomEquiv_pre_app {A B B' X : SSet.{u}}
    (i : B' ⟶ B) (f : A ⟶ (ihom B).obj X) :
    internalHomFlipHomEquiv A B' X (f ≫ (pre i).app X) =
      i ≫ internalHomFlipHomEquiv A B X f := by
  change curry ((β_ A B').hom ≫ uncurry (f ≫ (pre i).app X)) =
    i ≫ curry ((β_ A B).hom ≫ uncurry f)
  apply uncurry_injective
  rw [uncurry_curry, uncurry_pre_app, uncurry_natural_left, uncurry_curry]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality_right, Category.assoc]

/-- 概要：標的 X を固定した反変内部 Hom はその反対関手と随伴する。
方針：二変数の射の交換の同値と両変数の自然性を束ねる。
規約：左随伴は SSet から SSet の反対圏への関手。
使われ方：Kerodon §4.6.2（Tag 01HM） の前合成の持ち上げ条件の交換。 -/
noncomputable def internalHomFlipAdjunction (X : SSet.{u}) :
    (internalHom.flip.obj X).rightOp ⊣ internalHom.flip.obj X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B ↦
        (opEquiv (Opposite.op ((ihom A).obj X)) B).trans
          (internalHomFlipHomEquiv (Opposite.unop B) A X)
      homEquiv_naturality_left_symm := by
        intro A A' B f g
        apply Quiver.Hom.unop_inj
        exact internalHomFlipHomEquiv_pre f g
      homEquiv_naturality_right := by
        intro A B B' f g
        exact internalHomFlipHomEquiv_pre g.unop f.unop }

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
