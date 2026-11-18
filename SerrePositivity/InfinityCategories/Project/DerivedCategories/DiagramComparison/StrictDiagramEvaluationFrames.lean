module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramReedyMappingModel
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom

/-!
概要：元のReedy図式のsource frameとfibrant targetを、元の各複体へ評価する。
方針：Reedy射の既存の成分則と評価の余極限保存により、同じframeの条件を運ぶ。
規約：評価した解像を新しい無関係な選択へ置き換えない。
使われ方：Hovey §5.4、HTT 4.2.4.4の全変換空間の値の模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance isw1StrictDiagramEvaluationFramesLocal1 : ModelCategory (Complex A) := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
local instance isw1StrictDiagramEvaluationFramesLocal2 : HasLimitsOfSize.{0, 0} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasLimitsOfShape⟩
local instance isw1StrictDiagramEvaluationFramesLocal3 : HasColimitsOfSize.{0, 0} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance isw1StrictDiagramEvaluationFramesLocal4 : HasInitial (Complex A) := (isZero_zero (Complex A)).isInitial.hasInitial
local instance isw1StrictDiagramEvaluationFramesLocal5 : HasTerminal (Complex A) := (isZero_zero (Complex A)).isTerminal.hasTerminal
local instance isw1StrictDiagramEvaluationFramesLocal6 : HasInitial (SimplexCategory ⥤ Complex A) :=
  (isZero_zero (SimplexCategory ⥤ Complex A)).isInitial.hasInitial
local instance isw1StrictDiagramEvaluationFramesLocal7 : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance isw1StrictDiagramEvaluationFramesLocal8 : HasInitial (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial
local instance isw1StrictDiagramEvaluationFramesLocal9 : HasTerminal (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isTerminal.hasTerminal

/-- Hovey §5.2のReedy射の成分則により、元の評価は両Quillen条件を満たす。 -/
lemma strictDiagramEvaluationAt_isQuillen (j : strictDiagramIndex d) :
    Quillen.IsLeftQuillen ((CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj j) ∧
    Quillen.IsRightQuillen ((CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj j) := by
  have hc : ∀ {X Y : StrictComplexDiagram A d} (f : X ⟶ Y),
      cofibrations (StrictComplexDiagram A d) f → cofibrations (Complex A) (f.app j) := by
    cases d with
    | simplicial => exact fun f hf => Reedy.cofibration_app Reedy.simplexOp f hf j
    | cosimplicial => exact fun f hf => Reedy.cofibration_app Reedy.simplex f hf j
  have hf : ∀ {X Y : StrictComplexDiagram A d} (f : X ⟶ Y),
      fibrations (StrictComplexDiagram A d) f → fibrations (Complex A) (f.app j) := by
    cases d with
    | simplicial => exact fun f hf => Reedy.fibration_app Reedy.simplexOp f hf j
    | cosimplicial => exact fun f hf => Reedy.fibration_app Reedy.simplex f hf j
  have hw : ∀ {X Y : StrictComplexDiagram A d} (f : X ⟶ Y),
      weakEquivalences (StrictComplexDiagram A d) f → weakEquivalences (Complex A) (f.app j) := by
    cases d <;> exact fun f h => h j
  exact ⟨⟨fun _ _ f h => hc f h, fun _ _ f h => ⟨hc f h.1, hw f h.2⟩⟩,
    ⟨fun _ _ f h => hf f h, fun _ _ f h => ⟨hf f h.1, hw f h.2⟩⟩⟩

/-- 図式圏の同じsource frameを、指定頂点で評価した余単体的複体。 -/
def strictDiagramEvaluatedSourceFrame (X : StrictComplexDiagram A d)
    (j : strictDiagramIndex d) : SimplexCategory ⥤ Complex A :=
  (strictDiagramSourceFrame A d X).obj ⋙ (CategoryTheory.evaluation _ _).obj j

/-- 評価はlatching余極限とcofibrationを保つため、同じ評価frameはReedy cofibrant。 -/
lemma strictDiagramEvaluatedSourceFrame_cofibrant (X : StrictComplexDiagram A d)
    (j : strictDiagramIndex d) :
    Reedy.reedyLeft Reedy.simplex (cofibrations (Complex A))
      (initial.to (strictDiagramEvaluatedSourceFrame A d X j)) := by
  exact Reedy.reedyCofibrant_of_preservesLatching Reedy.simplex
    ((CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj j)
    (strictDiagramSourceFrame A d X).obj (fun _ => inferInstance)
    (strictDiagramEvaluationAt_isQuillen A d j).1.map_cofibrations
    (strictDiagramSourceFrame A d X).cofibrant

/-- 同じframeの構造射の擬同型性は、同じ頂点で評価しても保たれる。 -/
lemma strictDiagramEvaluatedSourceFrame_homotopicallyConstant
    (X : StrictComplexDiagram A d) (j : strictDiagramIndex d)
    {m n : SimplexCategory} (a : m ⟶ n) :
    weakEquivalences (Complex A) ((strictDiagramEvaluatedSourceFrame A d X j).map a) := by
  have h := (strictDiagramSourceFrame A d X).homotopicallyConstant a
  cases d <;> exact h j

/-- 元のfibrant置換の各値も、Reedy fibrationの成分則によりfibrantである。 -/
lemma strictDiagramFibrantTarget_obj_isFibrant (Y : StrictComplexDiagram A d)
    (j : strictDiagramIndex d) : IsFibrant ((strictDiagramFibrantTarget A d Y).obj j) := by
  haveI := strictDiagramFibrantTarget_isFibrant A d Y
  have h : fibrations (StrictComplexDiagram A d)
      (terminal.from (strictDiagramFibrantTarget A d Y)) := (fibration_iff _).mp inferInstance
  have hp := (strictDiagramEvaluationAt_isQuillen A d j).2.map_fibrations _ h
  exact (isFibrant_iff_of_isTerminal
    (((CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj j).map
      (terminal.from (strictDiagramFibrantTarget A d Y)))
    (terminalIsTerminal.isTerminalObj ((CategoryTheory.evaluation _ _).obj j)
      (⊤_ (StrictComplexDiagram A d)))).mpr ⟨hp⟩

/-- 同じsource frameを全頂点で束ねる。添字射も元の自然変換の成分を使う。 -/
def strictDiagramEvaluatedSourceFrames (X : StrictComplexDiagram A d) :
    strictDiagramIndex d ⥤ (SimplexCategory ⥤ Complex A) :=
  (strictDiagramSourceFrame A d X).obj.flip

/-- Hovey §5.4の実Homを全ての始点・終点で束ねた、同じ二変数の単体集合。 -/
def strictDiagramPointFrameMapping (X Y : StrictComplexDiagram A d) :
    (strictDiagramIndex d)ᵒᵖ ⥤ strictDiagramIndex d ⥤ SSet.{u} :=
  (strictDiagramEvaluatedSourceFrames A d X).op ⋙
    CosimplicialHom.cosimplicialHomBifunctor ⋙
      (Functor.whiskeringLeft (strictDiagramIndex d) (Complex A) SSet.{u}).obj
        (strictDiagramFibrantTarget A d Y)

/-- 同じ二変数Homの各値は、評価frameのcofibrancyと標的のfibrancyからKanとなる。 -/
lemma strictDiagramPointFrameMapping_kanComplex (X Y : StrictComplexDiagram A d)
    (i : (strictDiagramIndex d)ᵒᵖ) (j : strictDiagramIndex d) :
    KanComplex (((strictDiagramPointFrameMapping A d X Y).obj i).obj j) := by
  haveI := strictDiagramFibrantTarget_obj_isFibrant A d Y j
  exact HomotopyFunctionComplex.cosimplicialHom_kanComplex
    (strictDiagramEvaluatedSourceFrame A d X i.unop)
    (strictDiagramEvaluatedSourceFrame_cofibrant A d X i.unop)
    (strictDiagramEvaluatedSourceFrame_homotopicallyConstant A d X i.unop)
    ((strictDiagramFibrantTarget A d Y).obj j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
