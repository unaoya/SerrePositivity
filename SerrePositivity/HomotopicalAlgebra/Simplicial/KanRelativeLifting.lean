module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyExtension

/-!
# 境界pushout-productの持ち上げ性から指定した相対ホモトピーを延長する

## 概要
境界pushout-productの持ち上げ性から指定した相対ホモトピーを延長する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0431][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0431
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative homotopy extension from the actual boundary pushout-product lift

No monomorphism or weak-equivalence hypothesis is needed once the
specified lifting property has been supplied.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.KanRelativeLifting
variable {A B K : SSet.{v}} (i : A ⟶ B)

abbrev boundaryProduct := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
  (SSet.boundary 1).ι

/-- 境界pushout-productの持ち上げ性から指定した相対ホモトピーを延長する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma exists_extension
    (hl : HasLiftingProperty (boundaryProduct i).ι (terminal.from K))
    (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    ∃ V : SSet.Homotopy f g,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h := by
  let pp := boundaryProduct i
  have : HasLiftingProperty pp.ι (terminal.from K) := hl
  let b := pp.isPushout.desc (LargeParameterHomotopy.boundaryMap f g) H.h
    (KanHomotopyExtension.boundary_compatibility i f g H)
  let sq : CommSq b pp.ι (terminal.from K) (terminal.from _) := ⟨by simp⟩
  have hb : B ◁ (SSet.boundary 1).ι ≫ sq.lift =
      LargeParameterHomotopy.boundaryMap f g := by
    rw [show B ◁ (SSet.boundary 1).ι = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hH : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ sq.lift = H.h := by
    rw [show i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) = pp.inr ≫ pp.ι from
      pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  refine ⟨{ h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }, hH⟩
  · change SSet.ι₀ ≫ sq.lift = f
    rw [← LargeParameterHomotopy.section_zero B, Category.assoc,
      ← SSet.boundary.ι_ι (1 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · change SSet.ι₁ ≫ sq.lift = g
    rw [← LargeParameterHomotopy.section_one B, Category.assoc,
      ← SSet.boundary.ι_ι (0 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_one]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)


end SerrePositivity.SimplicialModel.KanRelativeLifting
