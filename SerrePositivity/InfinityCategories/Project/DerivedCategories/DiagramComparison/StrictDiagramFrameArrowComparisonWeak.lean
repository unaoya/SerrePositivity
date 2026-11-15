module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowConeHom

/-!
概要：元のframe arrow錐からBK endへの指定比較射は単体的ホモトピー同値。
方針：元の自由増大射のHomの同値性と、指定比較への保存等式を合成する。
使われ方：HTT 4.2.4.4、RR02(a)の実BK比較の結論。
規約：通常の極限性だけからホモトピー極限性を推論せず、元の射の分解を用いる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape

/-- 元のframe Homからの指定BK比較は、同じ射としてホモトピー同値。 -/
lemma strictDiagramFrameArrowComparison_equivalence (X Y : StrictComplexDiagram A d) :
    IsSimplicialHomotopyEquivalence (strictDiagramFrameArrowComparison A d X Y) := by
  have isoWeak {U V : SSet.{u}} (e : U ≅ V) :
      IsSimplicialHomotopyEquivalence e.hom := by
    refine ⟨e.inv, ?_, ?_⟩
    · rw [e.hom_inv_id]
      exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 U))⟩
    · rw [e.inv_hom_id]
      exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 V))⟩
  haveI := strictDiagramFibrantTarget_isFibrant A d Y
  haveI := SerrePositivity.HomotopyFunctionComplex.cosimplicialHom_kanComplex
    (strictDiagramSourceFrame A d X).obj (strictDiagramSourceFrame A d X).cofibrant
    (strictDiagramSourceFrame A d X).homotopicallyConstant (strictDiagramFibrantTarget A d Y)
  haveI : SSet.KanComplex ((cosimplicialHom
      (SSet.stdSimplex ⋙ FrameWeightRealization.bousfieldKanParameterRealization
        (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X))).obj
          (strictDiagramFibrantTarget A d Y)) :=
    SerrePositivity.HomotopyFunctionComplex.cosimplicialHom_kanComplex
    (strictDiagramFreeArrowRealizedFrame A d X)
    (strictDiagramFreeArrowRealizedFrame_cofibrant A d X)
    (strictDiagramFreeArrowRealizedFrame_homotopicallyConstant A d X)
    (strictDiagramFibrantTarget A d Y)
  haveI := SerrePositivity.HomotopyFunctionComplex.cosimplicialHom_kanComplex
    (strictDiagramFreeArrowRealizedFrame A d X)
    (strictDiagramFreeArrowRealizedFrame_cofibrant A d X)
    (strictDiagramFreeArrowRealizedFrame_homotopicallyConstant A d X)
    (strictDiagramFibrantTarget A d Y)
  let e := ((FrameWeightRealization.bousfieldKanRealizationHomIso
    (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X)).app
      (strictDiagramFibrantTarget A d Y)) ≪≫
    bousfieldKanOpOpIso (StrictDiagramArrowElements.{u} d) _ ≪≫
      (weightedSectionsFunctor (bousfieldKanWeight (StrictDiagramArrowElements.{u} d))).mapIso
        (strictDiagramFreeArrowHomNatIso A d X Y)
  haveI := kanComplex_of_iso e
  apply (congrArg IsSimplicialHomotopyEquivalence
    (strictDiagramFreeArrowConeHom_eq A d X Y)).mp
  exact (strictDiagramFreeArrowAugmentationHom_equivalence A d X Y).comp (isoWeak e)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
