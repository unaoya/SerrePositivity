module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarPointwiseInvariance
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# 始対象での定値図式から全図式の bar への比較

概要：全遷移が反転される図式に、元の始対象からの比較を与える。
方針：始対象の唯一の射を自然変換へ束ね、bar の成分不変性を適用する。
規約：始対象は明示的に指定する。単体集合モデルは要求しない。
使われ方：恒等右脚から全右脚への Hom 図式の比較。
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows
open _root_.SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
  {i : D} (hi : IsInitial i)

/-- 元の始対象から各対象への唯一の射による図式の自然変換。 -/
def fromInitial : (Functor.const D).obj (F.obj i) ⟶ F where
  app d := F.map (hi.to d)
  naturality {d e} f := by
    change 𝟙 _ ≫ F.map (hi.to e) = F.map (hi.to d) ≫ F.map f
    rw [Category.id_comp, ← F.map_comp]
    exact congrArg F.map (hi.hom_ext _ _)

/-- 全遷移が反転されるとき、始対象からの同じ bar の比較も反転される。 -/
lemma fromInitial_localized_isIso
    (hF : ∀ {d e : D} (f : d ⟶ e),
      IsIso (AnodyneHomotopy.anodyneQ.map (F.map f))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((BarConstruction.functor D).map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.fromInitial F hi))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.map_localized_isIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.fromInitial F hi) (fun d => hF (hi.to d))

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows
