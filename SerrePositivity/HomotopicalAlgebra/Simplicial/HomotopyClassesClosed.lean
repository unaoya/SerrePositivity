module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# 閉構造の随伴を区間ホモトピー類の実際の全単射へ降下させる

## 概要
閉構造の随伴を区間ホモトピー類の実際の全単射へ降下させる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。
[棚卸し m0403][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0403
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The closed adjunction descends to actual interval homotopy classes

Reassociation retains the original interval parameter in currying and
uncurrying. No Kan condition is needed for the quotient equivalence.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.HomotopyClassesClosed
variable {A X K : SSet.{v}}

private lemma curry_endpoint (k : Bool) :
    A ◁ (if k then SSet.ι₁ (X := X) else SSet.ι₀) ≫
      (α_ A X (SSet.stdSimplex.obj (SimplexCategory.mk 1))).inv =
        (if k then SSet.ι₁ (X := A ⊗ X) else SSet.ι₀) := by
  cases k <;> apply NatTrans.ext <;> funext n <;>
    exact ConcreteCategory.hom_ext _ _ (fun x => rfl)

private lemma uncurry_endpoint (k : Bool) :
    (if k then SSet.ι₁ (X := A ⊗ X) else SSet.ι₀) ≫
      (α_ A X (SSet.stdSimplex.obj (SimplexCategory.mk 1))).hom =
        A ◁ (if k then SSet.ι₁ (X := X) else SSet.ι₀) := by
  cases k <;> apply NatTrans.ext <;> funext n <;>
    exact ConcreteCategory.hom_ext _ _ (fun x => rfl)

def curryHomotopy {f g : A ⊗ X ⟶ K} (H : SSet.Homotopy f g) :
    SSet.Homotopy (curry f) (curry g) where
  h := curry ((α_ A X _).inv ≫ H.h)
  h₀ := by
    change SSet.ι₀ ≫ curry ((α_ A X _).inv ≫ H.h) = curry f
    have he := curry_endpoint (A := A) (X := X) false
    simp only [Bool.false_eq_true, ite_false] at he
    rw [← curry_natural_left, ← Category.assoc, he, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ curry ((α_ A X _).inv ≫ H.h) = curry g
    have he := curry_endpoint (A := A) (X := X) true
    simp only [ite_true] at he
    rw [← curry_natural_left, ← Category.assoc, he, H.h₁]
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

def uncurryHomotopy {f g : X ⟶ (ihom A).obj K} (H : SSet.Homotopy f g) :
    SSet.Homotopy (uncurry f) (uncurry g) where
  h := (α_ A X _).hom ≫ uncurry H.h
  h₀ := by
    change SSet.ι₀ ≫ ((α_ A X _).hom ≫ uncurry H.h) = uncurry f
    have he := uncurry_endpoint (A := A) (X := X) false
    simp only [Bool.false_eq_true, ite_false] at he
    rw [← Category.assoc, he, ← uncurry_natural_left, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ ((α_ A X _).hom ≫ uncurry H.h) = uncurry g
    have he := uncurry_endpoint (A := A) (X := X) true
    simp only [ite_true] at he
    rw [← Category.assoc, he, ← uncurry_natural_left, H.h₁]
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

def curryClass : HomotopyClasses.obj (A ⊗ X) K → HomotopyClasses.obj X ((ihom A).obj K) :=
  Quot.map curry (fun _ _ ⟨H⟩ => ⟨curryHomotopy H⟩)

def uncurryClass : HomotopyClasses.obj X ((ihom A).obj K) → HomotopyClasses.obj (A ⊗ X) K :=
  Quot.map uncurry (fun _ _ ⟨H⟩ => ⟨uncurryHomotopy H⟩)

/-- 閉構造の随伴を区間ホモトピー類の実際の全単射へ降下させる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
def equiv : HomotopyClasses.obj (A ⊗ X) K ≃ HomotopyClasses.obj X ((ihom A).obj K) where
  toFun := curryClass
  invFun := uncurryClass
  left_inv x := Quot.inductionOn x (fun f => congrArg HomotopyClasses.mk (uncurry_curry f))
  right_inv x := Quot.inductionOn x (fun f => congrArg HomotopyClasses.mk (curry_uncurry f))

lemma uncurryClass_post {A B : SSet.{v}} (i : A ⟶ B)
    (x : HomotopyClasses.obj X ((ihom B).obj K)) :
    uncurryClass (HomotopyClasses.post ((MonoidalClosed.pre i).app K) x) =
      HomotopyClasses.pre (i ▷ X) (uncurryClass x) := by
  refine Quot.inductionOn x (fun f => ?_)
  exact congrArg HomotopyClasses.mk (uncurry_pre_app K f i)

end SerrePositivity.SimplicialModel.HomotopyClassesClosed
