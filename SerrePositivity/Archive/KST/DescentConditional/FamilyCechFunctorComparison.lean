module

public import SerrePositivity.Archive.KST.DescentConditional.FiniteFamilyCech
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# 有限被覆族の多重引き戻しの関手による指定比較

## 概要
有限 wide pullback を保つ関手で被覆族の幾何を移し、各 Čech 段の指定同型を構成する。

## 方針
元の wide cospan の像を指定 wide cospan と同定し、極限保存の標準同型を使う。
指定射影と全ての単体射についての可換性を証明する。

## 規約
終対象や非連結な有限極限の保存は要求しない。スライス圏の忘却に適用する。

## 使われ方
論文 公理 (1)、補題 3.2 の transfer の自然変換の定義域への被覆族の移送。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w t z

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {D : Type w} [Category.{t} D] [HasFiniteLimits D] (G : C ⥤ D)
  {ι : Type z} {Y : C} (X : ι → C) (cover : ∀ i, X i ⟶ Y)

/-- 概要：wide cospan の関手による像の指定同型（公理 (1)）。
方針：各頂点で恒等同型とし、元の関手が恒等射を保つことを使う。
規約：底の頂点と各成分の頂点を同時に保持。使われ方：極限保存の比較の終域。 -/
def mapWideCospanIso :
    WidePullbackShape.wideCospan Y X cover ⋙ G ≅
      WidePullbackShape.wideCospan (G.obj Y) (fun i ↦ G.obj (X i)) (fun i ↦ G.map (cover i)) :=
  WidePullbackShape.diagramIsoWideCospan (WidePullbackShape.wideCospan Y X cover ⋙ G)

variable [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1))) G]

/-- 概要：被覆族の各 Čech 段の関手による指定同型（公理 (1)）。
方針：指定極限保存の同型と wide cospan の指定同型を合成する。
規約：有限 wide pullback の保存だけを使う。使われ方：Over の忘却による被覆族の比較。 -/
def familyCechTermFunctorIso (n : SimplexCategory) (a : Fin (n.len + 1) → ι) :
    G.obj (familyCechTerm X cover n a) ≅
      familyCechTerm (fun i ↦ G.obj (X i)) (fun i ↦ G.map (cover i)) n a :=
  preservesLimitIso G (WidePullbackShape.wideCospan Y (fun j ↦ X (a j))
    (fun j ↦ cover (a j))) ≪≫
      HasLimit.isoOfNatIso (mapWideCospanIso G (fun j ↦ X (a j)) (fun j ↦ cover (a j)))

/-- 概要：指定比較は各座標の射影を保つ（公理 (1)）。
方針：極限比較の射影の公式を合成する。
規約：元の指定射の像に厳密に一致。使われ方：単体射の自然性。 -/
theorem familyCechTermFunctorIso_hom_π (n : SimplexCategory) (a : Fin (n.len + 1) → ι)
    (j : Fin (n.len + 1)) :
    (familyCechTermFunctorIso G X cover n a).hom ≫
        WidePullback.π (fun j ↦ G.map (cover (a j))) j =
      G.map (WidePullback.π (fun j ↦ cover (a j)) j) := by
  simp [familyCechTermFunctorIso, WidePullback.π, mapWideCospanIso,
    WidePullbackShape.diagramIsoWideCospan]

/-- 概要：指定比較は基底への射影を保つ（公理 (1)）。
方針：極限比較の底頂点の公式を合成する。
規約：元の増強の指定射を保つ。使われ方：前層の指定増強の比較。 -/
theorem familyCechTermFunctorIso_hom_base (n : SimplexCategory) (a : Fin (n.len + 1) → ι) :
    (familyCechTermFunctorIso G X cover n a).hom ≫
        WidePullback.base (fun j ↦ G.map (cover (a j))) =
      G.map (WidePullback.base (fun j ↦ cover (a j))) := by
  simp [familyCechTermFunctorIso, WidePullback.base, mapWideCospanIso,
    WidePullbackShape.diagramIsoWideCospan]

/-- 概要：指定比較は全ての被覆族 Čech の単体射を保つ（公理 (1)）。
方針：全ての座標射影と底射影で極限比較の式を使う。
規約：段ごとの抽象同型に弱めない。使われ方：前層を写した余単体比較の自然性。 -/
theorem familyCechTermFunctorIso_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (a : Fin (m.len + 1) → ι) :
    G.map (familyCechMap X cover f a) ≫
        (familyCechTermFunctorIso G X cover n (fun j ↦ a (f.toOrderHom j))).hom =
      (familyCechTermFunctorIso G X cover m a).hom ≫
        familyCechMap (fun i ↦ G.obj (X i)) (fun i ↦ G.map (cover i)) f a := by
  apply WidePullback.hom_ext
  · intro j
    simp only [Category.assoc, familyCechTermFunctorIso_hom_π,
      familyCechMap, WidePullback.lift_π, ← G.map_comp]
  · simp only [Category.assoc, familyCechTermFunctorIso_hom_base,
      familyCechMap, WidePullback.lift_base, ← G.map_comp]

/-- 概要：指定比較の逆も全ての単体射を保つ（公理 (1)）。
方針：指定比較の自然性と同型の逆関係で計算する。
規約：元の幾何の合成の等式。使われ方：反変前層で写した比較の自然性。 -/
theorem familyCechTermFunctorIso_inv_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (a : Fin (m.len + 1) → ι) :
    (familyCechTermFunctorIso G X cover m a).inv ≫ G.map (familyCechMap X cover f a) =
      familyCechMap (fun i ↦ G.obj (X i)) (fun i ↦ G.map (cover i)) f a ≫
        (familyCechTermFunctorIso G X cover n (fun j ↦ a (f.toOrderHom j))).inv := by
  apply (cancel_mono
    (familyCechTermFunctorIso G X cover n (fun j ↦ a (f.toOrderHom j))).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [familyCechTermFunctorIso_naturality]
  simp

end SerrePositivity.KST.Descent
