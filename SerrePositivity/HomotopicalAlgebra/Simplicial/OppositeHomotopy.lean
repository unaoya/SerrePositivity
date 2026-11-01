module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction

/-!
# 単体方向を反転したaugmentationも指定された条件のもとで局所化可逆となる

## 概要
単体方向を反転したaugmentationも指定された条件のもとで局所化可逆となる。
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
[棚卸し m0506][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0506
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reversing the simplex direction reverses interval homotopies
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.OppositeHomotopy

abbrev reverse (X : SSet.{v}) : SSet.{v} := SimplexCategory.rev.op ⋙ X
abbrev reverseMap {X Y : SSet.{v}} (f : X ⟶ Y) : reverse X ⟶ reverse Y :=
  Functor.whiskerLeft SimplexCategory.rev.op f

abbrev intervalIso : reverse SimplexPrefix.interval.{v} ≅ SimplexPrefix.interval.{v} :=
  SSet.stdSimplex.opIso (SimplexCategory.mk 1)

def cylinderMap (X : SSet.{v}) : reverse X ⊗ SimplexPrefix.interval ⟶
    reverse (X ⊗ SimplexPrefix.interval) where
  app n := ↾fun x => (x.1, intervalIso.inv.app n x.2)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · exact types_congr_hom (intervalIso.inv.naturality θ) x.2

lemma cylinderMap_zero (X : SSet.{v}) :
    SSet.ι₀ ≫ cylinderMap X = reverseMap (SSet.ι₁ (X := X)) := by
  ext n x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    rfl

lemma cylinderMap_one (X : SSet.{v}) :
    SSet.ι₁ ≫ cylinderMap X = reverseMap (SSet.ι₀ (X := X)) := by
  ext n x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    rfl

def homotopy {X Y : SSet.{v}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (reverseMap g) (reverseMap f) where
  h := cylinderMap X ≫ reverseMap H.h
  h₀ := by rw [← Category.assoc, cylinderMap_zero]; exact congrArg reverseMap H.h₁
  h₁ := by rw [← Category.assoc, cylinderMap_one]; exact congrArg reverseMap H.h₀
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

abbrev doubleIso (X : SSet.{v}) : reverse (reverse X) ≅ X :=
  SSet.opFunctorCompOpFunctorIso.app X

variable {A : SimplicialObject.Augmented (Type v)}
  (ed : SimplicialObject.Augmented.ExtraDegeneracy A)
  {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
def reversedComparisonIso : L.obj (reverse A.left) ≅
    L.obj (reverse ((SimplicialObject.const (Type v)).obj A.right)) :=
  AnodyneHomotopy.mapRetractionIso L hL (reverseMap A.hom) (reverseMap ed.section_)
    (congrArg reverseMap ed.section_comp_hom)
    (homotopy (ExtraDegeneracyContraction.contraction ed))

include ed in
/-- 単体方向を反転したaugmentationも指定された条件のもとで局所化可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma localized_reversed_augmentation_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (reverseMap A.hom)) :=
  (reversedComparisonIso ed AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)).isIso_hom

end SerrePositivity.SimplicialModel.OppositeHomotopy
