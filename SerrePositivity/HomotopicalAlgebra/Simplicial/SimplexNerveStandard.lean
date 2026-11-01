module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveMonos
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveInitialContraction
public import Mathlib.CategoryTheory.Elements

/-!
# 標準単体に対する単体圏nerveのaugmentationは指定局所化で可逆となる

## 概要
標準単体に対する単体圏nerveのaugmentationは指定局所化で可逆となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0567][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0567
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The standard simplex augmentation is inverted without a simplicial model

Both actual terminal maps are inverted using explicit initial-object
contractions. This is the standard-simplex case, not the general theorem.
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SimplexNerve

def standardRepresentation (n : SimplexCategory) :
    (SSet.stdSimplex.{v}.obj n).RepresentableBy n where
  homEquiv := SSet.stdSimplex.objEquiv.symm
  homEquiv_comp _ _ := rfl

abbrev standardInitial (n : SimplexCategory) : (SSet.stdSimplex.{v}.obj n).Elements :=
  Functor.Elements.initialOfRepresentableBy (standardRepresentation n)

def standardIsInitial (n : SimplexCategory) : IsInitial (standardInitial.{v} n) :=
  Functor.Elements.isInitialOfRepresentableBy (standardRepresentation n)

def ordinalIsInitial (n : ℕ) : IsInitial (ULift.up (0 : Fin (n + 1)) : ULift.{v} _) :=
  IsInitial.ofUniqueHom (fun _ => homOfLE (Fin.zero_le _)) (fun _ _ => Subsingleton.elim _ _)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma standardTerminal_isIso (n : ℕ) :
    IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)))) := by
  let e := SSet.stdSimplex.isoNerve.{v} n
  have : IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (ULift.{v} (Fin (n + 1)))))) :=
    inferInstanceAs (IsIso (NerveInitialImage.terminalImageIso (ordinalIsInitial n) L hL).hom)
  have ht : SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.{v}.obj
      (SimplexCategory.mk n)) = e.hom ≫ SSet.stdSimplex.isTerminalObj₀.from _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht, L.map_comp]
  infer_instance

include hL in
/-- 標準単体に対する単体圏nerveのaugmentationは指定局所化で可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。
-/
lemma standardAugmentation_isIso (n : ℕ) :
    IsIso (L.map ((augmentation.{v}).app (SSet.stdSimplex.obj (SimplexCategory.mk n)))) := by
  let X := SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)
  have : IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from X)) :=
    standardTerminal_isIso L hL n
  have : IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from (nerve X.Elements))) :=
    inferInstanceAs (IsIso (NerveInitialImage.terminalImageIso
      (standardIsInitial (SimplexCategory.mk n)) L hL).hom)
  have ht : (augmentation.app X) ≫ SSet.stdSimplex.isTerminalObj₀.from X =
      SSet.stdSimplex.isTerminalObj₀.from (nerve X.Elements) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have : IsIso (L.map (augmentation.app X) ≫ L.map (SSet.stdSimplex.isTerminalObj₀.from X)) := by
    rw [← L.map_comp, ht]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp this

end SerrePositivity.SimplicialModel.SimplexNerve
