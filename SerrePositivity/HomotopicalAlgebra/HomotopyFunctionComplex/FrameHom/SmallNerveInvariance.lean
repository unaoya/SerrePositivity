module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall

/-!
# 元の nerve の反転性を同じ小圏の比較へ移す

概要：元の関手の nerve の反転性は、対象・射の宇宙を揃えても保存される。
方針：元の射列の up/down の同型と同じ宇宙拡大の自然性を使う。
規約：同じ関手と全単体作用素を保持し、大きい宇宙にもモデル構造を置かない。
使われ方：元の Hom の反対要素圏の不変性を小さい分解の図式へ移す。
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerve
open _root_.SerrePositivity.SimplicialModel

variable {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)

/-- 元の関手の前後で対象と射を同じ上限へ揃える。 -/
abbrev functor : AsSmall.{w} C ⥤ AsSmall.{w} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- 元の射列の down による二つの同型は同じ関手の比較と可換。 -/
lemma naturality :
    nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerve.functor.{u, v, w} F) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall.iso D).hom =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall.iso C).hom ≫ SSet.uliftFunctor.map (nerveMap F) := by
  ext n c
  rfl

/-- 元の nerve の射そのものの反転性を、同じ小さい関手の nerve へ移す。 -/
lemma map_localized_isIso (hF : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap F))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerve.functor.{u, v, w} F))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (SSet.uliftFunctor.{w, max u v}.map (nerveMap F))) :=
    UniverseLift.anodyneQ_map_isIso_of_small _ hF
  have h := congrArg AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerve.naturality.{u, v, w} F)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerve.functor.{u, v, w} F)) ≫
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall.iso D).hom) := h.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerve
