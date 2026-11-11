module

public import SerrePositivity.CategoryTheory.CechNerveData
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Čech データの関手と小さい同値模型への移送

## 概要
標準余積の Čech データと弱始性を、通常の関手や小さい同値模型へ移す。

## 方針
指定した余積の保存と同値の余単位を使う。

## 規約
BS 著者版 Construction 4.17–4.18 の古典的な入力。三つの宇宙を独立に取る。

## 使われ方
大きい prismatic site の Čech 対象を小さい site の対象として読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v u' v' w
namespace CategoryTheory
open Limits
open scoped Simplicial
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- 概要：圏同値は弱始対象を弱始対象へ送る。
方針：逆関手の対象への射と余単位の同型を合成する。
規約：BS 著者版 Construction 4.17 の移送。使われ方：小さい模型の零次の弱始性。 -/
theorem IsWeaklyInitial.map_equivalence {U : C} (hU : IsWeaklyInitial U) (e : C ≌ D) :
    IsWeaklyInitial (e.functor.obj U) := by
  intro V
  obtain ⟨f⟩ := hU (e.inverse.obj V)
  exact ⟨e.functor.map f ≫ (e.counitIso.app V).hom⟩

namespace CechNerveData

/-- 概要：標準余積を保つ関手で Čech の余積を移し、反対圏の積として読む。
方針：各余積の保存を ofCoproducts へ入力する。
規約：BS 著者版 Construction 4.18。一般の余積の存在は不要。
使われ方：同値模型や別の通常の圏への移送。 -/
def ofCoproductsMap (X : CosimplicialObject C)
    (hX : ∀ n : ℕ, IsColimit (Cofan.mk (X.obj ⦋n⦌)
      (fun i : Fin (n + 1) => X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))))
    (F : C ⥤ D)
    (hF : ∀ n : ℕ, PreservesColimit
      (Discrete.functor (fun _ : Fin (n + 1) => X.obj ⦋0⦌)) F) :
    CechNerveData (Opposite.op (F.obj (X.obj ⦋0⦌))) :=
  ofCoproducts (X ⋙ F) (fun n => by
    letI := hF n
    exact isColimitCofanMkObjOfIsColimit F _ _ (hX n))

/-- 概要：標準余積の余単体的対象を小さい同値模型の Čech データへ移す。
方針：小さい模型との同値が余積を保つことを使う。
規約：BS 著者版 Construction 4.18。対象の宇宙を w に縮める。
使われ方：小さい prismatic site の Čech 脈体。 -/
def ofCoproductsSmall [EssentiallySmall.{w} C] (X : CosimplicialObject C)
    (hX : ∀ n : ℕ, IsColimit (Cofan.mk (X.obj ⦋n⦌)
      (fun i : Fin (n + 1) => X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)))) :
    CechNerveData (Opposite.op ((equivSmallModel.{w} C).functor.obj (X.obj ⦋0⦌))) :=
  ofCoproductsMap X hX (equivSmallModel.{w} C).functor (fun _ => inferInstance)

/-- 概要：弱始対象の小さい同値模型は、反対圏で弱終対象。
方針：同値で弱始性を移し、射を反転する。
規約：BS 著者版 Construction 4.17。使われ方：小さい site の Čech 対象。 -/
theorem weaklyTerminal_small [EssentiallySmall.{w} C] {U : C} (hU : IsWeaklyInitial U) :
    IsWeaklyTerminal (Opposite.op ((equivSmallModel.{w} C).functor.obj U)) :=
  weaklyTerminal_op (hU.map_equivalence (equivSmallModel.{w} C))

end CechNerveData
end CategoryTheory
