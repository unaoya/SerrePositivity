module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarIdentity

/-!
# 恒等barの収縮区間が全単体作用素と整合する

## 概要
恒等barの収縮区間が全単体作用素と整合する。
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
[棚卸し m0523][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0523
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Compatibility of the identity-bar contraction interval with all simplicial operators
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

abbrev identityLevelMap (d : D) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :=
  ((commaLevels (𝟭 D) F).map θ).app d |>.toFunctor

abbrev contractionInterval (d : D) (n : SimplexCategoryᵒᵖ) :=
  SerrePositivity.NerveHomotopy.interval (identityContraction F d n)

lemma contractionInterval_operator_obj (d : D) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (z : Fin 2 × CostructuredArrow (elementProjection (𝟭 D) F n) d) :
    (contractionInterval F d n ⋙ identityLevelMap F d θ).obj z =
      ((𝟭 (Fin 2)).prod (identityLevelMap F d θ) ⋙ contractionInterval F d m).obj z := by
  rcases z with ⟨q, e⟩
  fin_cases q
  · rfl
  · exact congrArg (identityPoint F d m)
      (congrArg (fun k => k e.left.val) ((F.map e.hom).naturality θ)).symm

private lemma comma_hom_heq {n : SimplexCategoryᵒᵖ} {d : D}
    {e e' s s' : CostructuredArrow (elementProjection (𝟭 D) F n) d}
    (he : e = s) (he' : e' = s') (f : e ⟶ e') (g : s ⟶ s')
    (h : f.left.hom ≍ g.left.hom) : f ≍ g := by
  cases he
  cases he'
  apply heq_of_eq
  apply CostructuredArrow.hom_ext
  apply Functor.Elements.hom_ext
  exact eq_of_heq h

/- 旧宣言の技術注記：
The full interval functors commute, including the mixed 0→1 part.
-/
/-- 恒等barの収縮区間が全単体作用素と整合する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
lemma contractionInterval_operator (d : D) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    contractionInterval F d n ⋙ identityLevelMap F d θ =
      (𝟭 (Fin 2)).prod (identityLevelMap F d θ) ⋙ contractionInterval F d m := by
  apply CategoryTheory.Functor.hext (contractionInterval_operator_obj F d θ)
  intro x y f
  apply comma_hom_heq F
    (contractionInterval_operator_obj F d θ x) (contractionInterval_operator_obj F d θ y)
  rcases x with ⟨q, e⟩
  rcases y with ⟨r, e'⟩
  fin_cases q <;> fin_cases r
  · rfl
  · rfl
  · have h := leOfHom f.1
    change (1 : Fin 2) ≤ 0 at h
    exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
  · rfl

end SerrePositivity.SimplicialModel.BarConstruction
