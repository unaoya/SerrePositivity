module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarContractionOperators

/-!
# 恒等射影のbarの対角に一つの実単体的収縮を構成する

## 概要
恒等射影のbarの対角に一つの実単体的収縮を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0524][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0524
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A single model-free simplicial contraction of the identity-projection bar

The full interval compatibility, including its mixed part, glues all
nerve-degree contractions into the actual diagonal homotopy.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

/-- The same degreewise nerve interval, now natural in both simplicial directions together. -/
def identityHomotopyMap (d : D) :
    (relative (𝟭 D) F).obj d ⊗ SSet.stdSimplex.{max uD vD v}.obj (SimplexCategory.mk 1) ⟶
      (relative (𝟭 D) F).obj d where
  app n := (SerrePositivity.NerveHomotopy.hom (identityContraction F d n)).app n
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    let t := (SimplexCategory.toCat.map θ.unop).toFunctor
    let q := (SSet.stdSimplex.objEquiv x.2).toOrderHom.monotone.functor
    let z := (t ⋙ q).prod' (t ⋙ x.1)
    exact congrArg (fun J => z ⋙ J) (contractionInterval_operator F d θ).symm

lemma identityHomotopyMap_zero (d : D) :
    SSet.ι₀ ≫ identityHomotopyMap F d = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  have h := congrArg (fun k => k.app n c)
    (SerrePositivity.NerveHomotopy.at_zero (identityContraction F d n))
  exact h.trans (CategoryTheory.Functor.comp_id c)

lemma identityHomotopyMap_one (d : D) :
    SSet.ι₁ ≫ identityHomotopyMap F d =
      (identityAugmentation F).app d ≫ identitySection F d := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  have h := congrArg (fun k => k.app n c)
    (SerrePositivity.NerveHomotopy.at_one (identityContraction F d n))
  exact h.trans (identityCollapse_chain F d n c)

/- 旧宣言の技術注記：
An actual diagonal homotopy; it uses no model structure at the enlarged value universe.
-/
/-- 恒等射影のbarの対角に一つの実単体的収縮を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
def identityDiagonalHomotopy (d : D) :
    SSet.Homotopy (𝟙 ((relative (𝟭 D) F).obj d))
      ((identityAugmentation F).app d ≫ identitySection F d) where
  h := identityHomotopyMap F d
  h₀ := identityHomotopyMap_zero F d
  h₁ := identityHomotopyMap_one F d
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.SimplicialModel.BarConstruction
