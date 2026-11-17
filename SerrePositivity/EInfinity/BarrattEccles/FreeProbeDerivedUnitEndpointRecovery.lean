module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedUnitVertex
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedUnitRecoveryComponent
public import SerrePositivity.EInfinity.ComplexLimits.ProbeDerivedSourceVertex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.ConstantRestrictionArrow
/-!
概要：既存の標準導来単位成分を、元の複体単位の同じ端点へ回収する。
方針：元の全単位回収式を評価し、既存の端点同型の二射を相殺する。
規約：既存の標準単位と全比較を変更しない。
使われ方：局所化源での弱な単位比較を標準単位比較へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A)

private lemma componentEndpointCancellation {C : Type*} [Category* C]
    {a b c d e f g : C} (p : a ≅ b) (q : b ≅ c) (v : c ⟶ d)
    (r : d ≅ e) (s : d ≅ f) (t : f ≅ g) (w : a ⟶ g)
    (h : p.hom ≫ q.hom ≫ v ≫ s.hom ≫ t.hom = w) :
    (p ≪≫ q).hom ≫ (v ≫ r.hom) ≫ (r.symm ≪≫ s ≪≫ t).hom = w := by
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using h

/-- 概要：標準自由頂点の実 U 像と元の自由代数の底の複体頂点の同型。
方針：既存の自由源頂点比較・全忘却比較の評価・通常図式頂点比較を合成する。
規約：元の全比較を保持。使われ方：標準単位成分の元の単位への回収。 -/
def freeProbeDerivedUnitUnderlyingVertexIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
      (cAlgVertex A ((freeProbeFunctor A).obj X)))
      ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((freeProbeFunctor A).obj X).carrier)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (freeProbeCAlgSource_vertexIso A X) (cAlgForgetDerived A)).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate (freeProbeUnderlyingDerivedSourceIso A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≪≫
      complexDiagramDerivedVertexIso A (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X

/-- 概要：既存の probe 始域比較は同じ全源比較の評価と通常頂点輸送。
方針：既存の頂点成分と同じ二射の評価の一致を使う。
規約：元の比較そのもの。使われ方：標準単位回収式の始域側。 -/
lemma freeProbeDerivedUnit_probeVertexIso :
    complexProbeDerivedSourceVertexIso A X =
      (complexDiagramDerivedVertexIso A (ComplexLimits.framedLimitProbeFunctor A) X).symm ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate (complexProbeDerivedSourceIso A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate_eq_app]
  rfl

/-- 概要：元の全単位回収式の評価は同じ五つの端点射の全合成。
方針：同じ評価の合成保存で元の回収式を展開する。
規約：元の全比較の評価を保持。使われ方：標準単位成分の端点回収。 -/
lemma freeProbeDerivedUnitFullComponent_recovery :
    (complexDiagramDerivedVertexIso A (ComplexLimits.framedLimitProbeFunctor A) X).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (complexProbeDerivedSourceIso A).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeDerivedUnit A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeUnderlyingDerivedSourceIso A).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫
      (complexDiagramDerivedVertexIso A
        (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X).hom =
      freeProbeUnitOrdinaryHom A X := by
  have h := freeProbeDerivedUnitRecoveredHom_eq A X
  dsimp only [freeProbeDerivedUnitRecoveredHom] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp] at h
  simpa only [Category.assoc] using h

/-- 概要：標準単位成分を同じ両端で回収すると元の通常自由単位の導来像になる。
方針：元の全回収式の評価と同じ自由源頂点同型の逆則を使う。
規約：標準単位・元の単位成分・実 U を保持。使われ方：単位比較の端点整合。 -/
lemma freeProbeDerivedUnitComponent_recovery :
    (complexProbeDerivedSourceVertexIso A X).hom ≫ freeProbeDerivedUnitComponent A X ≫
      (freeProbeDerivedUnitUnderlyingVertexIso A X).hom = freeProbeUnitOrdinaryHom A X := by
  rw [freeProbeDerivedUnit_probeVertexIso]
  refine componentEndpointCancellation
    (complexDiagramDerivedVertexIso A (ComplexLimits.framedLimitProbeFunctor A) X).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate (complexProbeDerivedSourceIso A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeDerivedUnit A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (freeProbeCAlgSource_vertexIso A X) (cAlgForgetDerived A))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate (freeProbeUnderlyingDerivedSourceIso A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
    (complexDiagramDerivedVertexIso A
      (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X)
    (freeProbeUnitOrdinaryHom A X) ?_
  dsimp only [Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate]
  exact freeProbeDerivedUnitFullComponent_recovery A X

end SerrePositivity.EInfinity.BarrattEccles
