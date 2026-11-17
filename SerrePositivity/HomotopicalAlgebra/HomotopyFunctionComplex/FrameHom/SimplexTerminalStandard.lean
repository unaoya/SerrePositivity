module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalFunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveTerminalImage
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveStandard

/-!
# 標準単体上の終端 augmentation の実際の反転性

概要：反対要素圏の終端 augmentation は標準単体上で anodyne 反転後に可逆。
方針：元の標準単体と同じ反対要素圏の終射を実際の収縮で反転する。
規約：単体集合のモデル構造を要求しない。全単体集合の定理は後続。
使われ方：cellular な比較の反転性の標準単体の入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v uH vH

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

/-- 概要：標準単体の反対要素圏は元の単体を終対象として持つ（Dwyer–Kan §7）。
方針：同じ表現可能単体の要素圏の始対象を反対にする。
規約：元の標準単体の同じ要素圏。
使われ方：実際の nerve の終射の反転性。 -/
def standardIsTerminal (n : SimplexCategory) :
    IsTerminal (Opposite.op (SerrePositivity.SimplicialModel.SimplexNerve.standardInitial.{v} n)) :=
  (SerrePositivity.SimplicialModel.SimplexNerve.standardIsInitial n).op

include hL in
/-- 概要：標準単体の同じ終端 augmentation は anodyne 反転後に同型（Dwyer–Kan §7）。
方針：元の二つの終射の収縮による反転性と終対象への一意性を使う。
規約：比較射は構成済みの同じ augmentation。
使われ方：任意の単体集合への cellular な拡張の入力。 -/
lemma standardAugmentation_isIso (n : ℕ) :
    IsIso (L.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app (SSet.stdSimplex.obj (SimplexCategory.mk n)))) := by
  let K := SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)
  have : IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from K)) :=
    SerrePositivity.SimplicialModel.SimplexNerve.standardTerminal_isIso L hL n
  have : IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from (nerve K.Elementsᵒᵖ))) :=
    inferInstanceAs (IsIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveTerminalImage.terminalImageIso
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.standardIsTerminal (SimplexCategory.mk n)) L hL).hom)
  have ht : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K ≫ SSet.stdSimplex.isTerminalObj₀.from K =
      SSet.stdSimplex.isTerminalObj₀.from (nerve K.Elementsᵒᵖ) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have : IsIso (L.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K) ≫ L.map (SSet.stdSimplex.isTerminalObj₀.from K)) := by
    rw [← L.map_comp, ht]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp this

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve
