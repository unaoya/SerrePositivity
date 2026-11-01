module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 二つの区間を二項演算で同時に合成した族はパラメータ変更に自然である

## 概要
二つの区間を二項演算で同時に合成した族はパラメータ変更に自然である。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0401][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0401
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A binary operation transports two chosen intervals to one specified square

The two interval coordinates remain independent. All four edges are the
original chosen intervals with the other input fixed at its endpoint.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.HomotopyBinarySquare
abbrev interval : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 1)

abbrev firstParameter (T : SSet.{v}) : (T ⊗ interval) ⊗ interval ⟶ T ⊗ interval := fst _ _

def secondParameter (T : SSet.{v}) : (T ⊗ interval) ⊗ interval ⟶ T ⊗ interval where
  app _ := ↾fun x => (x.1.1, x.2)
  naturality _ _ _ := by ext x; rfl

lemma outer_zero_first (T : SSet.{v}) : SSet.ι₀ ≫ firstParameter T = 𝟙 _ := rfl
lemma outer_one_first (T : SSet.{v}) : SSet.ι₁ ≫ firstParameter T = 𝟙 _ := rfl
lemma outer_zero_second (T : SSet.{v}) :
    SSet.ι₀ ≫ secondParameter T = fst T interval ≫ SSet.ι₀ := rfl
lemma outer_one_second (T : SSet.{v}) :
    SSet.ι₁ ≫ secondParameter T = fst T interval ≫ SSet.ι₁ := rfl
lemma inner_zero_first (T : SSet.{v}) :
    (SSet.ι₀ (X := T)) ▷ interval ≫ firstParameter T = fst T interval ≫ SSet.ι₀ := rfl
lemma inner_one_first (T : SSet.{v}) :
    (SSet.ι₁ (X := T)) ▷ interval ≫ firstParameter T = fst T interval ≫ SSet.ι₁ := rfl
lemma inner_zero_second (T : SSet.{v}) :
    (SSet.ι₀ (X := T)) ▷ interval ≫ secondParameter T = 𝟙 _ := rfl
lemma inner_one_second (T : SSet.{v}) :
    (SSet.ι₁ (X := T)) ▷ interval ≫ secondParameter T = 𝟙 _ := rfl

variable {T A B K : SSet.{v}} {f₀ f₁ : T ⟶ A} {g₀ g₁ : T ⟶ B}
  (F : SSet.Homotopy f₀ f₁) (G : SSet.Homotopy g₀ g₁) (k : A ⊗ B ⟶ K)

def square : (T ⊗ interval) ⊗ interval ⟶ K :=
  lift (firstParameter T ≫ F.h) (secondParameter T ≫ G.h) ≫ k

lemma square_outer_zero : SSet.ι₀ ≫ square F G k =
    lift F.h (fst T interval ≫ g₀) ≫ k := by
  rw [square, ← Category.assoc, comp_lift, ← Category.assoc, ← Category.assoc,
    outer_zero_first, outer_zero_second, Category.id_comp, Category.assoc, G.h₀]

lemma square_outer_one : SSet.ι₁ ≫ square F G k =
    lift F.h (fst T interval ≫ g₁) ≫ k := by
  rw [square, ← Category.assoc, comp_lift, ← Category.assoc, ← Category.assoc,
    outer_one_first, outer_one_second, Category.id_comp, Category.assoc, G.h₁]

lemma square_inner_zero : (SSet.ι₀ (X := T)) ▷ interval ≫ square F G k =
    lift (fst T interval ≫ f₀) G.h ≫ k := by
  rw [square, ← Category.assoc, comp_lift, ← Category.assoc, ← Category.assoc,
    inner_zero_first, inner_zero_second, Category.id_comp, Category.assoc, F.h₀]

lemma square_inner_one : (SSet.ι₁ (X := T)) ▷ interval ≫ square F G k =
    lift (fst T interval ≫ f₁) G.h ≫ k := by
  rw [square, ← Category.assoc, comp_lift, ← Category.assoc, ← Category.assoc,
    inner_one_first, inner_one_second, Category.id_comp, Category.assoc, F.h₁]

def simultaneous : SSet.Homotopy (lift f₀ g₀ ≫ k) (lift f₁ g₁ ≫ k) where
  h := lift F.h G.h ≫ k
  h₀ := by rw [← Category.assoc, comp_lift, F.h₀, G.h₀]; rfl
  h₁ := by rw [← Category.assoc, comp_lift, F.h₁, G.h₁]; rfl
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

def diagonal (T : SSet.{v}) : T ⊗ interval ⟶ (T ⊗ interval) ⊗ interval :=
  lift (𝟙 _) (snd _ _)

lemma diagonal_square : diagonal T ≫ square F G k = (simultaneous F G k).h := by
  rw [square, ← Category.assoc, comp_lift]
  rfl

/-- 二つの区間を二項演算で同時に合成した族はパラメータ変更に自然である。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma simultaneous_naturality {U : SSet.{v}} (j : U ⟶ T) :
    (simultaneous (HomotopyClasses.preHomotopy j F) (HomotopyClasses.preHomotopy j G) k).h =
      j ▷ interval ≫ (simultaneous F G k).h := by
  change lift (j ▷ interval ≫ F.h) (j ▷ interval ≫ G.h) ≫ k =
    j ▷ interval ≫ (lift F.h G.h ≫ k)
  rw [← Category.assoc, comp_lift]

end SerrePositivity.SimplicialModel.HomotopyBinarySquare
