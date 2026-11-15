module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementDiagram
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleDiagramSource
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalCoconeSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NerveCoconePrism

/-!
概要：元の全 frame 評価 を同じ Hom 持ち上げ先の通常余錐にする。
方針：元の自然変換をそのまま後合成し、同じ余錐から終端付き列を作る。
規約：HA Construction 1.3.1.13、元の対象・射・全列。
使われ方：同じ全 slice 評価と元の通常 評価円柱の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementEvaluationCocone :
    Cocone (strictRawModuleTensorElementDiagram A X P Q ⋙
      ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)) where
  pt := ULiftHom.objUp Q
  ι := CategoryTheory.Functor.whiskerRight (strictRawModuleTensorElementEvaluation A X P Q)
    (ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X))

def strictRawModuleTensorElementEvaluatedColumn {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ComposableArrows (strictRawModuleCategory A X) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (strictRawModuleTensorElementEvaluationCocone A X P Q) c ⋙
      ULiftHom.down.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)

lemma strictRawModuleTensorElementEvaluatedColumn_obj_castSucc {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    (strictRawModuleTensorElementEvaluatedColumn A X P Q c).obj i.castSucc =
      (strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i) := by
  change ULiftHom.objDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (strictRawModuleTensorElementEvaluationCocone A X P Q) c).obj i.castSucc) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast]
  rfl

lemma strictRawModuleTensorElementEvaluatedColumn_obj_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementEvaluatedColumn A X P Q c).obj (Fin.last (n + 1)) =
      Q := by
  change ULiftHom.objDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (strictRawModuleTensorElementEvaluationCocone A X P Q) c).obj (Fin.last (n + 1))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_last]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
