module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 自然変換から圏のnerveの間の実単体的ホモトピーを構成する

## 概要
自然変換から圏のnerveの間の実単体的ホモトピーを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
自然変換を区間圏と元の圏の直積からの関手として表し、nerveに適用する。
各射列を単体として評価し、二つの端点と単体作用素との交換を確認する。

## 規約と注意
通常の圏と自然変換を入力し、圏が群oidであることは仮定しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0012][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/archive/k-theory-generalization-inventory.md#m0012
[plan]: ../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual simplicial homotopies induced by natural transformations

The interval diagram of functors is uncurried and evaluated on each
simplex and its monotone interval parameter. All dimensions use one formula.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.NerveHomotopy
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G : C ⥤ D} (α : F ⟶ G)

abbrev interval : Fin 2 × C ⥤ D := Functor.uncurry.obj (ComposableArrows.mk₁ α)

def hom : nerve C ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶ nerve D where
  app _n := ↾fun p => ((SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor.prod' p.1) ⋙
    interval α
  naturality {_ _} _ := rfl

@[reassoc]
lemma at_zero : SSet.ι₀ ≫ hom α = nerveMap F := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun E => ?_)
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ ≫ F.map (E.map h) = eqToHom rfl ≫ F.map (E.map h) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

@[reassoc]
lemma at_one : SSet.ι₁ ≫ hom α = nerveMap G := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun E => ?_)
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ ≫ G.map (E.map h) = eqToHom rfl ≫ G.map (E.map h) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 自然変換から圏のnerveの間の実単体的ホモトピーを構成する。

通常の圏と自然変換を入力し、圏が群oidであることは仮定しない。
自然変換を区間圏と元の圏の直積からの関手として表し、nerveに適用する。
各射列を単体として評価し、二つの端点と単体作用素との交換を確認する。
-/
def homotopy : SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := hom α
  h₀ := at_zero α
  h₁ := at_one α
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property


abbrev point (a : C) : SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) ⟶ nerve C :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₀ a)

lemma constant_eq (a : C) :
    SSet.stdSimplex.isTerminalObj₀.from (nerve C) ≫ point a =
      nerveMap ((Functor.const C).obj a) := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun E => ?_)
  rfl

end SerrePositivity.NerveHomotopy
