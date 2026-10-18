module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraRestrictionCoherence

/-!
概要：KST §3.1 の正規表示の標準局所加群制限同型の結合整合性。
方針：一対象での評価を通して標準同型の恒等成分を比較する。
規約：四つの頂点に対する二つの指定合成経路を等式として比較する。
使われ方：局所導来制限の擬関手の整合性の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：正規表示での局所 dg 遷移に沿う通常加群制限。
方針：一対象 dg 関手の二重 opposite に沿って制限する。
規約：KST §3.1。使われ方：標準制限同型の整合性を記述する。 -/
abbrev diagramAlgebraModuleRestriction {i j : J} (h : i ≤ j) :=
  moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op.op

set_option maxHeartbeats 2000000 in
-- 四頂点の標準制限同型の対象と合成を照合するために必要。
/-- 概要：三段の局所制限の標準合成同型は結合整合性を満たす。
方針：加群射を標準点で評価し、四つの標準同型の恒等成分を使う。
規約：KST §3.1。使われ方：導来制限の標準合成同型の四頂点整合性。 -/
theorem diagramAlgebraRestrictionCompIso_assoc {i j k l : J}
    (h : i ≤ j) (g : j ≤ k) (t : k ≤ l)
    (M : ModuleCategory R (AlgebraVertex (F.obj l))ᵒᵖ) :
    (diagramAlgebraRestrictionCompIso F h g).hom.app
        ((diagramAlgebraModuleRestriction F t).obj M) ≫
        (diagramAlgebraRestrictionCompIso F (h.trans g) t).hom.app M =
      (diagramAlgebraModuleRestriction F h).map
        ((diagramAlgebraRestrictionCompIso F g t).hom.app M) ≫
        (diagramAlgebraRestrictionCompIso F h (g.trans t)).hom.app M := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [Functor.map_comp, Functor.map_comp,
    diagramAlgebraRestrictionCompIso_hom_eval, diagramAlgebraRestrictionCompIso_hom_eval,
    moduleRestriction_map_eval]
  change 𝟙 _ ≫ 𝟙 _ =
    (moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
      ((diagramAlgebraRestrictionCompIso F g t).hom.app M) ≫
      (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
        ((diagramAlgebraRestrictionCompIso F h (g.trans t)).hom.app M)
  rw [diagramAlgebraRestrictionCompIso_hom_eval, diagramAlgebraRestrictionCompIso_hom_eval]
  rfl

end SerrePositivity.KST.DerivedBlowup
