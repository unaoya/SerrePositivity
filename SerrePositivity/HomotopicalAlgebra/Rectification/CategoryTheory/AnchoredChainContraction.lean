module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.AnchoredChainNerve
public import SerrePositivity.CategoryTheory.NerveHomotopy

/-!
# 中断した任意モデル源への一般化：AnchoredChainContraction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A simultaneous simplicial contraction of all anchored chains。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0002][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0002
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A simultaneous simplicial contraction of all anchored chains

The actual natural transformation from the source factorization induces a
nerve homotopy. It is transported through the previously proved simplicial
isomorphism, so all dimensions and ordinal operators use one contraction.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.AnchoredChain
variable {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V)

abbrev nerveCollapse : nerve (ArrowFactorization g) ⟶
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) :=
  SSet.stdSimplex.isTerminalObj₀.from _

abbrev nervePoint : SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) ⟶
    nerve (ArrowFactorization g) := NerveHomotopy.point (ArrowFactorization.source g)

def nerveContraction : SSet.Homotopy (nerveCollapse g ≫ nervePoint g)
    (𝟙 (nerve (ArrowFactorization g))) := by
  rw [nerveCollapse, nervePoint, NerveHomotopy.constant_eq]
  exact NerveHomotopy.homotopy (ArrowFactorization.fromSourceNatTrans g)

abbrev collapse : simplicial g ⟶ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) :=
  (nerveIso g).inv ≫ nerveCollapse g

abbrev basePoint : SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) ⟶ simplicial g :=
  nervePoint g ≫ (nerveIso g).hom

@[reassoc]
lemma basePoint_collapse : basePoint g ≫ collapse g = 𝟙 _ :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The whole chain parameter, not just each individual dimension, contracts to one point. -/
def contraction : SSet.Homotopy (collapse g ≫ basePoint g) (𝟙 (simplicial g)) where
  h := (nerveIso g).inv ▷ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
    (nerveContraction g).h ≫ (nerveIso g).hom
  h₀ := by
    calc
      _ = (nerveIso g).inv ≫ (SSet.ι₀ ≫ (nerveContraction g).h) ≫ (nerveIso g).hom := by
        rw [← Category.assoc, SSet.ι₀_comp]
        simp only [Category.assoc]
      _ = collapse g ≫ basePoint g := by
        rw [SSet.Homotopy.h₀]
        simp only [collapse, basePoint, Category.assoc]
  h₁ := by
    calc
      _ = (nerveIso g).inv ≫ (SSet.ι₁ ≫ (nerveContraction g).h) ≫ (nerveIso g).hom := by
        rw [← Category.assoc, SSet.ι₁_comp]
        simp only [Category.assoc]
      _ = 𝟙 _ := by rw [SSet.Homotopy.h₁, Category.id_comp, Iso.inv_hom_id]
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.AnchoredChain
