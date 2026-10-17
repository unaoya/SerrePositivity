module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionOperators
public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic

/-!
# 余モナドの面と退化の関係式を用いて表示単体圏上のaugmentation自然変換を構成する

## 概要
余モナドの面と退化の関係式を用いて表示単体圏上のaugmentation自然変換を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。

## 規約と注意
任意の圏と余モナドを入力し、モデル構造・局所可呈示性は要求しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0076][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0076
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The comonad resolution on the category presented by simplicial identities

All six defining relations are proved and the functor actually descends
to their quotient. No equivalence with the usual simplex category is
assumed: that comparison is a separate remaining construction.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.ComonadResolutionPresentation
open ComonadResolutionOperators
variable {C : Type u} [Category.{v} C] (G : Comonad C) (X : C)

def generators : FreeSimplexQuiver ⥤q Cᵒᵖ where
  obj n := Opposite.op (power G X (n.len + 1))
  map f := match f with
    | @FreeSimplexQuiver.Hom.δ n i => (face G X (n + 1) i).op
    | @FreeSimplexQuiver.Hom.σ n i => (degeneracy G X n i).op

def pathDiagram : Paths FreeSimplexQuiver ⥤ Cᵒᵖ := Paths.lift (generators G X)

lemma pathDiagram_obj (n : ℕ) :
    (pathDiagram G X).obj ((Paths.of FreeSimplexQuiver).obj (FreeSimplexQuiver.mk n)) =
      Opposite.op (power G X (n + 1)) := rfl

lemma pathDiagram_face {n : ℕ} (i : Fin (n + 2)) :
    (pathDiagram G X).map ((Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.δ i)) =
      (face G X (n + 1) i).op := Paths.lift_toPath (generators G X) _

lemma pathDiagram_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (pathDiagram G X).map ((Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.σ i)) =
      (degeneracy G X n i).op := Paths.lift_toPath (generators G X) _

lemma respects {a b : Paths FreeSimplexQuiver} {p q : a ⟶ b}
    (h : FreeSimplexQuiver.homRel p q) : (pathDiagram G X).map p = (pathDiagram G X).map q := by
  cases h with
  | @δ_comp_δ n i j h =>
    simpa only [CategoryTheory.Functor.map_comp, pathDiagram_face, op_comp] using
      congrArg Quiver.Hom.op (face_face G X (n + 1) i j h)
  | @δ_comp_σ_of_le n i j h =>
    simpa only [CategoryTheory.Functor.map_comp, pathDiagram_face, pathDiagram_degeneracy,
      op_comp] using congrArg Quiver.Hom.op (degeneracy_face_le G X n i j h)
  | @δ_comp_σ_self n i =>
    simpa only [CategoryTheory.Functor.map_comp, pathDiagram_face, pathDiagram_degeneracy,
      CategoryTheory.Functor.map_id, pathDiagram_obj, op_comp, op_id] using
      congrArg Quiver.Hom.op (degeneracy_face_self G X n i)
  | @δ_comp_σ_succ n i =>
    simpa only [CategoryTheory.Functor.map_comp, pathDiagram_face, pathDiagram_degeneracy,
      CategoryTheory.Functor.map_id, pathDiagram_obj, op_comp, op_id] using
      congrArg Quiver.Hom.op (degeneracy_face_succ G X n i)
  | @δ_comp_σ_of_gt n i j h =>
    simpa only [CategoryTheory.Functor.map_comp, pathDiagram_face, pathDiagram_degeneracy,
      op_comp] using congrArg Quiver.Hom.op (degeneracy_face_gt G X n i j h)
  | @σ_comp_σ n i j h =>
    simpa only [CategoryTheory.Functor.map_comp, pathDiagram_degeneracy, op_comp] using
      congrArg Quiver.Hom.op (degeneracy_degeneracy G X n i j h)

def oppositeDiagram : SimplexCategoryGenRel ⥤ Cᵒᵖ :=
  CategoryTheory.Quotient.lift _ (pathDiagram G X) (fun _ _ _ _ h => respects G X h)

def diagram : SimplexCategoryGenRelᵒᵖ ⥤ C := (oppositeDiagram G X).leftOp

lemma diagram_obj (n : ℕ) :
    (diagram G X).obj (Opposite.op (SimplexCategoryGenRel.mk n)) = power G X (n + 1) := rfl

lemma oppositeDiagram_face {n : ℕ} (i : Fin (n + 2)) :
    (oppositeDiagram G X).map (SimplexCategoryGenRel.δ i) = (face G X (n + 1) i).op :=
  Paths.lift_toPath (generators G X) (FreeSimplexQuiver.δ i)

lemma oppositeDiagram_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (oppositeDiagram G X).map (SimplexCategoryGenRel.σ i) = (degeneracy G X n i).op :=
  Paths.lift_toPath (generators G X) (FreeSimplexQuiver.σ i)

lemma diagram_face {n : ℕ} (i : Fin (n + 2)) :
    (diagram G X).map (SimplexCategoryGenRel.δ i).op = face G X (n + 1) i :=
  congrArg Quiver.Hom.unop (oppositeDiagram_face G X i)

lemma diagram_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (diagram G X).map (SimplexCategoryGenRel.σ i).op = degeneracy G X n i :=
  congrArg Quiver.Hom.unop (oppositeDiagram_degeneracy G X i)

lemma augmentation_naturality {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    (augmentation G X (a.len + 1)).op ≫ (oppositeDiagram G X).map f =
      (augmentation G X (b.len + 1)).op := by
  induction f using SimplexCategoryGenRel.hom_induction with
  | id =>
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  | comp_δ f i ih =>
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ih, oppositeDiagram_face]
    exact congrArg Quiver.Hom.op (face_augmentation G X _ i)
  | comp_σ f i ih =>
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ih, oppositeDiagram_degeneracy]
    exact congrArg Quiver.Hom.op (degeneracy_augmentation G X _ i)

/-- 余モナドの面と退化の関係式を用いて表示単体圏上のaugmentation自然変換を構成する。

任意の圏と余モナドを入力し、モデル構造・局所可呈示性は要求しない。
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。
-/
def augmentationNatTrans : diagram G X ⟶ (Functor.const _).obj X where
  app n := augmentation G X (n.unop.len + 1)
  naturality {n m} θ := by
    change (diagram G X).map θ ≫ augmentation G X (m.unop.len + 1) =
      augmentation G X (n.unop.len + 1) ≫ 𝟙 X
    rw [Category.comp_id]
    exact congrArg Quiver.Hom.unop (augmentation_naturality G X θ.unop)

end SerrePositivity.HomotopyFunctionComplex.ComonadResolutionPresentation
