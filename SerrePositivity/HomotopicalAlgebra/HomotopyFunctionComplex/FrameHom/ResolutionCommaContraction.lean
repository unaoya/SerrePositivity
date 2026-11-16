module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLiftComma
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage

/-!
# 分解から自明 fibration への comma 圏の可縮性

概要：Low 命題 3.6 の右 asphericity に現れる元の comma 圏の終射を反転する。
方針：全持ち上げ単体の反対要素圏との同値と同じ fiber の実際の収縮を使う。
規約：全次数の comma 圏を扱い、単体集合のモデル構造を要求しない。
使われ方：特殊な三本矢への共通比較の右射のホモトピー余終性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uH vH

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (A : SimplexCategory ⥤ C) {X E B : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  (p : E ⟶ B) [Fibration p] [WeakEquivalence p] (f : X ⟶ B)

include hA in
/-- 概要：元の comma 圏の nerve は anodyne 反転後に点と同型（Low 命題 3.6）。
方針：全持ち上げ単体の圏同値の像と元の終射の一意性から移す。
規約：順射は元の comma 圏の nerve の終射そのもの。
使われ方：分解の asphericity の全対象での判定。 -/
lemma commaTerminal_image_isIso {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.overFunctor A a f) (Over.mk p))))) := by
  have : IsIso (L.map (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.toComma A a p f))) :=
    inferInstanceAs (IsIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.commaEquivalence A a p f) L hL).hom)
  have : IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (LiftSpace.obj A a p f).Elementsᵒᵖ))) :=
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.elementsTerminal_image_isIso A a hA p f L hL
  have h : nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.toComma A a p f) ≫ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.overFunctor A a f) (Over.mk p))) =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (LiftSpace.obj A a p f).Elementsᵒᵖ) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have : IsIso (L.map (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.toComma A a p f)) ≫
      L.map (SSet.stdSimplex.isTerminalObj₀.from
        (nerve (CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.overFunctor A a f) (Over.mk p))))) := by
    rw [← L.map_comp, h]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp this

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift
