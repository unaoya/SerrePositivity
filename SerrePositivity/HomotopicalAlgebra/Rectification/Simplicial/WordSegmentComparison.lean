module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordSegment
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 中断した任意モデル源への一般化：WordSegmentComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The finite-word segment and the interval agree in anodyne localization。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0618][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0618
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The finite-word segment and the interval agree in anodyne localization

The explicit contraction supplies an inverse to the terminal projection.
The original interval maps into the word segment by an invertible map after
anodyne localization, without a model structure in the parameter universe.
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.WordSegmentComparison
open WordSegment

abbrev point : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 0)

def projection : obj.{v} ⟶ point := SSet.stdSimplex.isTerminalObj₀.from obj

lemma section_projection (s : point.{v} ⟶ obj) : s ≫ projection = 𝟙 point :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma projection_isIso : IsIso (L.map projection) :=
  (AnodyneHomotopy.mapRetractionIso L hL projection zero
    (section_projection zero) contraction).isIso_hom

include hL in
lemma unit_isIso : IsIso (L.map unit) := by
  have : IsIso (L.map projection) := projection_isIso L hL
  have hs : L.map unit ≫ L.map projection = 𝟙 _ := by
    rw [← L.map_comp, section_projection, L.map_id]
  exact (isIso_comp_right_iff _ (L.map projection)).mp
    (hs.symm ▸ inferInstanceAs (IsIso (𝟙 (L.obj point))))

include hL in
lemma letter_isIso : IsIso (L.map letter) := by
  have : IsIso (L.map (SSet.stdSimplex.δ (1 : Fin 2))) :=
    hL _ (AnodyneHomotopy.delta_anodyne 1 0 (by decide))
  have : IsIso (L.map unit) := unit_isIso L hL
  have hs : L.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫ L.map letter = L.map unit := by
    rw [← L.map_comp, vertex_zero_letter]
  exact (isIso_comp_left_iff (L.map (SSet.stdSimplex.δ (1 : Fin 2))) _).mp
    (hs.symm ▸ inferInstanceAs (IsIso (L.map unit)))

lemma localized_projection_isIso : IsIso (AnodyneHomotopy.anodyneQ.map projection.{v}) :=
  projection_isIso _ (Localization.inverts _ _)

lemma localized_letter_isIso : IsIso (AnodyneHomotopy.anodyneQ.map letter.{v}) :=
  letter_isIso _ (Localization.inverts _ _)

end SerrePositivity.SimplicialModel.WordSegmentComparison
