module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Equivalence

/-!
# 圏同値の元の nerve の射の anodyne 反転後の同型

概要：Low 命題 3.6 の comma 表示の圏同値を元の nerve の比較へ移す。
方針：同じ単位・余単位の自然変換のホモトピーから逆射の二つの法則を得る。
規約：単体集合モデルや nerve の Kan 性を仮定しない。
使われ方：持ち上げ空間の可縮性を実際の comma 圏へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uH vH

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage

open _root_.CategoryTheory
open _root_.SerrePositivity.SimplicialModel

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (e : C ≌ D) {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

/-- 概要：圏同値の元の nerve の射は anodyne 反転後に同型（Low 命題 3.6）。
方針：同じ逆関手の nerve と元の単位・余単位のホモトピーを使う。
規約：同型の順射は元の順関手の nerve の像。
使われ方：全持ち上げ単体の表示と comma 圏の可縮性の比較。 -/
def imageIso : L.obj (nerve C) ≅ L.obj (nerve D) where
  hom := L.map (nerveMap e.functor)
  inv := L.map (nerveMap e.inverse)
  hom_inv_id := by
    have h := AnodyneHomotopy.map_homotopy_eq L hL (_root_.SerrePositivity.NerveHomotopy.homotopy e.unitIso.hom)
    change L.map (𝟙 (nerve C)) = L.map (nerveMap e.functor ≫ nerveMap e.inverse) at h
    rw [L.map_id, L.map_comp] at h
    exact h.symm
  inv_hom_id := by
    have h := AnodyneHomotopy.map_homotopy_eq L hL (_root_.SerrePositivity.NerveHomotopy.homotopy e.counitIso.hom)
    change L.map (nerveMap e.inverse ≫ nerveMap e.functor) = L.map (𝟙 (nerve D)) at h
    rw [L.map_id, L.map_comp] at h
    exact h

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage
