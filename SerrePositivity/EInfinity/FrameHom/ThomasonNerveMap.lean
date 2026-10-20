module

public import SerrePositivity.EInfinity.FrameHom.ThomasonSimplex
public import SerrePositivity.EInfinity.FrameHom.BarValueInclusion

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
open CategoryTheory

namespace SerrePositivity.EInfinity.FrameHom.Thomason
open SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] (G : D ⥤ Cat.{vC, uC})

/-- 元の nerve の bar から同じ Grothendieck 全図式の nerve への比較。 -/
def map : (BarConstruction.functor D).obj (nerveDiagram G) ⟶
    nerve (Grothendieck G) where
  app _ := ↾fun e => simplex G e
  naturality {n m} θ := by
    ext e
    exact simplex_operator G e θ.unop

/-- 同じ fiber の射列の宇宙を上げて全図式へ入れる、元の nerve の包含。 -/
def fiberNerveMap (d : D) :
    SSet.uliftFunctor.{max uD vD, max uC vC}.obj (nerve (G.obj d)) ⟶
      nerve (Grothendieck G) where
  app _ := ↾fun e => e.down ⋙ Grothendieck.ι G d
  naturality _ _ _ := rfl

/-- 値の包含の後の比較は、同じ fiber の元の包含の nerve に厳密に一致。 -/
lemma valueInclusion_map (d : D) :
    BarRows.valueInclusion (nerveDiagram G) d ≫ map G = fiberNerveMap G d := by
  ext n e
  rfl

/-- 同じ全図式の射列の基底は元の bar の基底射列。 -/
lemma simplex_base {n : ℕ} (e : ComposableArrows (values G n).Elements n) :
    simplex G e ⋙ Grothendieck.forget G = e ⋙ Functor.Elements.π (values G n) := rfl

/-- 各対角頂点は、元の第 j 基底対象とその fiber の第 j 頂点。 -/
lemma map_vertex {n : ℕ} (e : ComposableArrows (values G n).Elements n)
    (j : Fin (n + 1)) :
    ((map G).app (Opposite.op (SimplexCategory.mk n)) e).obj j =
      ⟨(e.obj j).obj, (e.obj j).val.obj j⟩ := rfl

end SerrePositivity.EInfinity.FrameHom.Thomason
