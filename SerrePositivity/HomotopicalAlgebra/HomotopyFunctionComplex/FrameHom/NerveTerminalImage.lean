module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# 終対象を持つ圏の nerve の元の終射の反転

概要：終対象の収縮により元の nerve の終射を anodyne 反転後に同型へ送る。
方針：恒等関手から同じ定値関手への自然変換の実際のホモトピーを使う。
規約：単体集合のモデル構造や群oid 条件を要求しない。
使われ方：反対要素圏の標準単体での終端 augmentation の反転性。
-/

@[expose] public section

noncomputable section

universe u v uH vH

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveTerminalImage

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {a : C} (ha : IsTerminal a)

/-- 概要：同じ終対象への収縮は元の関手の自然変換（Dwyer–Kan §7）。
方針：終対象への一意な射を各成分に使う。
規約：元の恒等関手と定値関手を保持する。
使われ方：元の nerve の実際の収縮。 -/
def contraction : 𝟭 C ⟶ (Functor.const C).obj a where
  app c := ha.from c
  naturality _ _ _ := ha.hom_ext _ _

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

/-- 概要：同じ nerve の終射は anodyne を反転する任意の関手で同型（Dwyer–Kan §7）。
方針：元の終対象の頂点包含と実際の収縮のホモトピーを逆射に使う。
規約：同型の順射は元の nerve の終射の像。
使われ方：標準単体の反対要素圏の反転性。 -/
def terminalImageIso : L.obj (nerve C) ≅
    L.obj (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0)) where
  hom := L.map (SSet.stdSimplex.isTerminalObj₀.from (nerve C))
  inv := L.map (_root_.SerrePositivity.NerveHomotopy.point a)
  hom_inv_id := by
    rw [← L.map_comp, _root_.SerrePositivity.NerveHomotopy.constant_eq]
    have h := SerrePositivity.SimplicialModel.AnodyneHomotopy.map_homotopy_eq L hL
      (_root_.SerrePositivity.NerveHomotopy.homotopy (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveTerminalImage.contraction ha))
    exact h.symm.trans (L.map_id _)
  inv_hom_id := by
    rw [← L.map_comp]
    have h : _root_.SerrePositivity.NerveHomotopy.point a ≫ SSet.stdSimplex.isTerminalObj₀.from (nerve C) = 𝟙 _ :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, L.map_id]

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveTerminalImage
