module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# 通常の圏における Čech 脈体のデータ

## 概要
指定した対象の有限冪を、射影とその普遍性を含む単体的対象として扱う。

## 方針
一般の有限積の存在を課さず、必要な積錐だけをデータとして持つ。

## 規約
BS 著者版 Construction 4.17–4.18 の古典的な入力。対象と射の宇宙は独立。

## 使われ方
環の向きの余積を反転して prismatic site の Čech 脈体として読む。
-/

@[expose] public noncomputable section
universe u v u' v'
namespace CategoryTheory
open Limits
open scoped Simplicial
variable {C : Type u} [Category.{v} C]

/-- 概要：任意の対象から射を持つ弱終対象。
方針：射の存在だけを要求する。規約：BS 著者版 Construction 4.17 の site の向き。
使われ方：Čech データの始めの対象。 -/
def IsWeaklyTerminal (U : C) : Prop := ∀ V : C, Nonempty (V ⟶ U)

/-- 概要：任意の対象へ射を持つ弱始対象。
方針：弱終対象の双対として射の存在を要求する。
規約：BS 著者版 Construction 4.17 の環の向き。使われ方：包絡の弱始性。 -/
def IsWeaklyInitial (U : C) : Prop := ∀ V : C, Nonempty (U ⟶ V)

/-- 概要：各項が同じ対象の有限冪であることを明示した Čech 脈体。
方針：射影、積の普遍性、単体射に対する射影の整合性をまとめる。
規約：BS 著者版 Construction 4.18、通常の圏のみ。
使われ方：prismatic site の Čech 対象の古典的な入力。 -/
structure CechNerveData (U : C) where
  obj : SimplicialObject C
  proj : ∀ (n : ℕ) (i : Fin (n + 1)), obj.obj (Opposite.op ⦋n⦌) ⟶ U
  isLimit : ∀ n : ℕ, IsLimit (Fan.mk (obj.obj (Opposite.op ⦋n⦌)) (proj n))
  proj_map : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)),
    obj.map θ.op ≫ proj m i = proj n (θ.toOrderHom i)

namespace CechNerveData

/-- 概要：標準頂点を脚とする余積の余単体的対象から Čech 脈体を得る。
方針：反対圏で余積を積へ移し、定値の単体射の合成で射影の整合性を確認する。
規約：BS 著者版 Construction 4.17–4.18。一般の余積の存在は仮定しない。
使われ方：環の側の Čech–Alexander 対象を site の向きへ移す。 -/
def ofCoproducts (X : CosimplicialObject C)
    (hX : ∀ n : ℕ, IsColimit (Cofan.mk (X.obj ⦋n⦌)
      (fun i : Fin (n + 1) => X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)))) :
    CechNerveData (Opposite.op (X.obj ⦋0⦌)) where
  obj := X.op
  proj n i := (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).op
  isLimit n := Cofan.IsColimit.op (hX n)
  proj_map θ i := by
    change (X.map (SimplexCategory.const ⦋0⦌ _ i) ≫ X.map θ).op = _
    rw [← X.map_comp, SimplexCategory.const_comp]

/-- 概要：必要な有限冪を保つ関手に沿って Čech データを移す。
方針：各積錐の保存と関手の合成保存を使う。
規約：BS 著者版 Construction 4.18、対象と射の宇宙は独立。
使われ方：小さい同値模型への移送など、通常の圏の変更。 -/
def map {D : Type u'} [Category.{v'} D] {U : C} (d : CechNerveData U) (F : C ⥤ D)
    (hF : ∀ n : ℕ, PreservesLimit (Discrete.functor (fun _ : Fin (n + 1) => U)) F) :
    CechNerveData (F.obj U) where
  obj := d.obj ⋙ F
  proj n i := F.map (d.proj n i)
  isLimit n := by
    letI := hF n
    exact isLimitFanMkObjOfIsLimit F _ (d.proj n) (d.isLimit n)
  proj_map θ i := by
    change F.map (d.obj.map θ.op) ≫ F.map (d.proj _ i) = _
    rw [← F.map_comp, d.proj_map]

/-- 概要：余積の余単体的対象の零次の弱始性は Čech データの弱終性を与える。
方針：反対圏で射を反転する。
規約：BS 著者版 Construction 4.17。使われ方：site の Čech 対象の弱終性。 -/
theorem weaklyTerminal_op {U : C} (hU : IsWeaklyInitial U) :
    IsWeaklyTerminal (Opposite.op U) := by
  intro V
  obtain ⟨f⟩ := hU V.unop
  exact ⟨f.op⟩

end CechNerveData
end CategoryTheory
