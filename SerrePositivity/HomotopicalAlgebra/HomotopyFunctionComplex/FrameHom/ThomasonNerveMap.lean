module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonSimplex
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarValueInclusion

/-!
# bar から Grothendieck 全図式の nerve への元の比較射

概要：元の二方向の射列の対角から、全図式の nerve への実際の射を構成する。
方針：全作用素での単体の交換を使い、同じ fiber 包含との厳密な整合を示す。
規約：値と添字の宇宙は独立。構成だけから弱同値性は主張しない。
使われ方：Low 定理1.6 の比較と元の固定右脚の nerve の射の照合。
-/

@[expose] public section
universe uD vD uC vC
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason
open _root_.SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] (G : D ⥤ Cat.{vC, uC})

/-- 元の nerve の bar から同じ Grothendieck 全図式の nerve への比較。 -/
def map : (BarConstruction.functor D).obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram G) ⟶
    nerve (Grothendieck G) where
  app _ := ↾fun e => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex G e
  naturality {n m} θ := by
    ext e
    exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex_operator G e θ.unop

/-- 同じ fiber の射列の宇宙を上げて全図式へ入れる、元の nerve の包含。 -/
def fiberNerveMap (d : D) :
    SSet.uliftFunctor.{max uD vD, max uC vC}.obj (nerve (G.obj d)) ⟶
      nerve (Grothendieck G) where
  app _ := ↾fun e => e.down ⋙ Grothendieck.ι G d
  naturality _ _ _ := rfl

/-- 値の包含の後の比較は、同じ fiber の元の包含の nerve に厳密に一致。 -/
lemma valueInclusion_map (d : D) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.valueInclusion (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram G) d ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map G = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.fiberNerveMap G d := by
  ext n e
  rfl

/-- 同じ全図式の射列の基底は元の bar の基底射列。 -/
lemma simplex_base {n : ℕ} (e : ComposableArrows (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n).Elements n) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex G e ⋙ Grothendieck.forget G = e ⋙ Functor.Elements.π (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n) := rfl

/-- 各対角頂点は、元の第 j 基底対象とその fiber の第 j 頂点。 -/
lemma map_vertex {n : ℕ} (e : ComposableArrows (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n).Elements n)
    (j : Fin (n + 1)) :
    ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map G).app (Opposite.op (SimplexCategory.mk n)) e).obj j =
      ⟨(e.obj j).obj, (e.obj j).val.obj j⟩ := rfl

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason
