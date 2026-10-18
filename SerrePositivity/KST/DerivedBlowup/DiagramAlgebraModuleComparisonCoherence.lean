module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraModuleComparisonComponents
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraRestrictionCoherence

/-!
概要：KST §3.1 の一対象正規表示による指定局所加群比較の単位・三重整合性。
方針：全 Hom の評価の単射性で underlying 複体図式の関手性へ戻す。
規約：標準制限単位・合成同型を介する指定射の等式として述べる。
使われ方：正規表示における canonical な導来比較の整合性の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：恒等包含の指定局所加群比較は標準制限単位同型を介して恒等。
方針：標準点の評価で underlying 図式の恒等保存へ戻す。
規約：KST §3.1。使われ方：導来比較の単位条件の入力。 -/
theorem diagramAlgebraModuleComparison_id (i : J) (M : AllDiagramModules F) :
    diagramAlgebraModuleComparison F (le_refl i) M ≫
      (diagramAlgebraRestrictionIdIso F i).hom.app
        ((diagramAlgebraModuleEvaluation F i).obj M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  have hx : x = op .point := by
    apply Opposite.unop_injective
    cases x.unop
    rfl
  subst x
  rw [Functor.map_comp, CategoryTheory.Functor.map_id, diagramAlgebraModuleComparison_eval,
    diagramAlgebraRestrictionIdIso_hom_eval]
  change (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map
    (homOfLE (le_refl i)) ≫ 𝟙 _ = 𝟙 _
  simpa only [Category.comp_id] using
    diagramModuleUnderlyingDiagram_id F (ForgetEnrichment.to (Complex R) M) i

set_option maxHeartbeats 2000000 in
-- 三つの頂点の加群制限と標準合成同型の成分の型を照合するために必要。
/-- 概要：二段の指定局所加群比較は標準制限合成同型を介して直接比較に一致する。
方針：標準点での四成分の評価から underlying 図式の合成保存を使う。
規約：KST §3.1、同型の存在だけでなく指定経路の等式。
使われ方：主局所化への三重整合性の移送の入力。 -/
theorem diagramAlgebraModuleComparison_comp {i j k : J} (h : i ≤ j) (g : j ≤ k)
    (M : AllDiagramModules F) :
    diagramAlgebraModuleComparison F h M ≫
      (moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op.op).map (diagramAlgebraModuleComparison F g M) ≫
      (diagramAlgebraRestrictionCompIso F h g).hom.app
        ((diagramAlgebraModuleEvaluation F k).obj M) =
      diagramAlgebraModuleComparison F (h.trans g) M := by
  apply moduleMorphism_ext
  intro x
  have hx : x = op .point := by
    apply Opposite.unop_injective
    cases x.unop
    rfl
  subst x
  rw [Functor.map_comp, Functor.map_comp, diagramAlgebraModuleComparison_eval,
    diagramAlgebraRestrictionCompIso_hom_eval, moduleRestriction_map_eval,
    diagramAlgebraModuleComparison_eval_any, diagramAlgebraModuleComparison_eval]
  change (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) ≫
      (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map (homOfLE g) ≫
        𝟙 _ =
    (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map (homOfLE (h.trans g))
  simpa only [Category.comp_id] using
    (diagramModuleUnderlyingDiagram_comp F (ForgetEnrichment.to (Complex R) M) h g).symm

end SerrePositivity.KST.DerivedBlowup
