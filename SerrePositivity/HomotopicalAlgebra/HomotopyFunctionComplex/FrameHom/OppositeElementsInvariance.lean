module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalEquivalence

/-!
# 元の反対要素圏の nerve の不変性

概要：元の単体集合の比較が反転されれば、同じ反対要素圏の nerve の射も反転。
方針：既存の終端 augmentation の自然性と両成分の反転性を使う。
規約：通常の要素圏と反対要素圏を区別し、単体集合モデルは仮定しない。
使われ方：元の全右脚の Hom の不変性を全単体の圏の不変性へ移す。
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve
open _root_.SerrePositivity.SimplicialModel

/-- 元の係数射から来る反対要素圏の nerve の射そのものも反転される。 -/
lemma map_localized_isIso {K L : SSet.{v}} (f : K ⟶ L)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap f.mapElements.op)) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation_localized_isIso K
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation_localized_isIso L
  have h := congrArg AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.naturality f)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  change AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor.map f) ≫
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app L) =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K) ≫
        AnodyneHomotopy.anodyneQ.map f at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor.map f) ≫
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app L)) := h.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve
