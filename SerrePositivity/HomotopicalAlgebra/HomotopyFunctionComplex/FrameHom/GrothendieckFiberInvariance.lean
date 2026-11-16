module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonInversion

/-!
# 不変な Cat 値図式の元の fiber 包含の反転

概要：始対象を持ち全遷移の nerve が反転される図式では、各 fiber の包含も反転。
方針：同じ bar の値の包含と Thomason 比較の厳密な因子分解を合成する。
規約：同じ宇宙の小圏。元の fiber の nerve の Kan 性は要求しない。
使われ方：元の固定右脚から全右脚の図式への比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason
open _root_.SerrePositivity.SimplicialModel

variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u})

/-- 元の各 fiber の包含そのものは、始対象と全遷移の不変性から反転される。 -/
lemma fiberNerveMap_localized_isIso {i : D} (hi : IsInitial i)
    (hG : ∀ {d e : D} (f : d ⟶ e),
      IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (G.map f).toFunctor))) (d : D) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.fiberNerveMap G d)) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.valueInclusion_localized_isIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram G) hi hG d
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_localized_isIso G
  rw [← _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.valueInclusion_map, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason
