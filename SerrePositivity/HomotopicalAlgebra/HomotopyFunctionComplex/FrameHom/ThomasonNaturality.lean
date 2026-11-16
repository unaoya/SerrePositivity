module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonNerveMap

/-!
# Thomason 比較の元の係数自然性

概要：Cat 値図式の比較を、同じ bar と全図式の nerve の可換正方形へ送る。
方針：各対角頂点と元の移送の射を評価し、等式による移送を合成する。
規約：元の自然変換からの Grothendieck.map の射そのものを使う。
使われ方：固定右脚の図式から全左脚への比較との厳密な整合。
-/

@[expose] public section
universe uD vD uC vC
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason
open _root_.SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] {G H : D ⥤ Cat.{vC, uC}}

/-- 元の各成分の functor の nerve による自然変換。 -/
abbrev nerveComparison (α : G ⟶ H) : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram G ⟶ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram H :=
  Functor.whiskerRight α nerveFunctor

/-- 元の二重射列の対角は、同じ係数比較の全図式への像と厳密に可換。 -/
lemma simplex_naturality (α : G ⟶ H) {n : ℕ}
    (e : ComposableArrows (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n).Elements n) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex G e ⋙ Grothendieck.map α =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex H (e ⋙ (Functor.whiskerRight (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveComparison α)
        ((evaluation SimplexCategoryᵒᵖ (Type (max uC vC))).obj
          (Opposite.op (SimplexCategory.mk n)))).mapElements) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ rfl ?_
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex, Functor.comp_map, Grothendieck.map]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map, Cat.eqToHom_app,
    ← Category.assoc, eqToHom_trans]
  rfl

/-- 元の自然変換の bar と同じ全図式の nerve の比較は厳密に可換。 -/
lemma map_naturality (α : G ⟶ H) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map G ≫ nerveMap (Grothendieck.map α) =
      (BarConstruction.functor D).map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveComparison α) ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map H := by
  ext n e
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex_naturality α e

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason
