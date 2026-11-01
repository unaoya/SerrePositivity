module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 対象と射の宇宙を分けたまま自然変換からnerveのホモトピーを構成する

## 概要
対象と射の宇宙を分けたまま自然変換からnerveのホモトピーを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
自然変換を区間圏と元の圏の直積からの関手として表し、nerveに適用する。
各射列を単体として評価し、二つの端点と単体作用素との交換を確認する。

## 規約と注意
対象とHomの宇宙は独立に保ち、両nerveを明示した共通宇宙へULiftする。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0013][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0013
[plan]: ../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Nerve homotopies with independent object and Hom universes

Both nerves are explicitly lifted to a common value universe. The maps
and interval retain their actual chains, including their original arrows.
-/

@[expose] public section
universe uC vC uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.NerveHomotopyUniverse
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

def map (F : C ⥤ D) : SSet.uliftFunctor.{max uD vD, max uC vC}.obj (nerve C) ⟶
    SSet.uliftFunctor.{max uC vC, max uD vD}.obj (nerve D) where
  app _ := ↾fun c => ULift.up (c.down ⋙ F)
  naturality {_ _} _ := rfl

variable {F G : C ⥤ D} (α : F ⟶ G)

abbrev interval : Fin 2 × C ⥤ D := Functor.uncurry.obj (ComposableArrows.mk₁ α)

def hom : SSet.uliftFunctor.{max uD vD, max uC vC}.obj (nerve C) ⊗
    SSet.stdSimplex.{max uC vC uD vD}.obj (SimplexCategory.mk 1) ⟶
      SSet.uliftFunctor.{max uC vC, max uD vD}.obj (nerve D) where
  app _ := ↾fun p => ULift.up
    (((SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor.prod' p.1.down) ⋙ interval α)
  naturality {_ _} _ := rfl

/-- 独立した宇宙で構成したnerveのホモトピーの始点が指定した関手に一致する。

対象とHomの宇宙は独立に保ち、両nerveを明示した共通宇宙へULiftする。
自然変換を区間圏と元の圏の直積からの関手として表し、nerveに適用する。
各射列を単体として評価し、二つの端点と単体作用素との交換を確認する。
-/
lemma at_zero : SSet.ι₀ ≫ hom α = map F := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ ≫ F.map (c.down.map h) =
    eqToHom rfl ≫ F.map (c.down.map h) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

lemma at_one : SSet.ι₁ ≫ hom α = map G := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ ≫ G.map (c.down.map h) =
    eqToHom rfl ≫ G.map (c.down.map h) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 対象と射の宇宙を分けたまま自然変換からnerveのホモトピーを構成する。

対象とHomの宇宙は独立に保ち、両nerveを明示した共通宇宙へULiftする。
自然変換を区間圏と元の圏の直積からの関手として表し、nerveに適用する。
各射列を単体として評価し、二つの端点と単体作用素との交換を確認する。
-/
def homotopy : SSet.Homotopy (map F) (map G) where
  h := hom α
  h₀ := at_zero α
  h₁ := at_one α
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.NerveHomotopyUniverse
