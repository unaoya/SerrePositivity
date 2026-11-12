module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# hornの小対象論法で作った置換の値が全hornに対する右持ち上げ性を持つ

## 概要
hornの小対象論法で作った置換の値が全hornに対する右持ち上げ性を持つ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0342][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0342
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A value-side Kan replacement from the horn small-object argument alone

The chosen factorization and its unit are actual functorial data. No
model structure, weak-equivalence class, or source replacement is assumed.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.AnodyneKanReplacement

@[kerodon 00UV]
def factorization : MorphismProperty.FunctorialFactorizationData
    SSet.anodyneExtensions.{v} SSet.modelCategoryQuillen.J.rlp := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  exact MorphismProperty.functorialFactorizationData _ _

def terminalArrows : SSet.{v} ⥤ Arrow SSet.{v} where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _) (by simp)

abbrev functor : SSet.{v} ⥤ SSet.{v} := terminalArrows ⋙ factorization.Z

def unit : 𝟭 SSet.{v} ⟶ functor where
  app X := factorization.i.app (Arrow.mk (terminal.from X))
  naturality {_ _} f := factorization.i.naturality (terminalArrows.map f)

lemma unit_anodyne (X : SSet.{v}) : SSet.anodyneExtensions ((unit.{v}).app X) :=
  factorization.hi _

/-- hornの小対象論法で作った置換の値が全hornに対する右持ち上げ性を持つ。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma terminal_rlp (X : SSet.{v}) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((functor.{v}).obj X)) := by
  have h := factorization.hp (Arrow.mk (terminal.from X))
  have he : terminal.from (functor.obj X) =
      factorization.p.app (Arrow.mk (terminal.from X)) := terminal.hom_ext _ _
  rw [he]
  exact h

end SerrePositivity.SimplicialModel.AnodyneKanReplacement
