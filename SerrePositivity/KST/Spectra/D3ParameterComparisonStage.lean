module

public import SerrePositivity.KST.Spectra.D3ParameterUnitComparison
public import SerrePositivity.KST.Spectra.D3GradedWhiskeringHom

/-!
概要：共同パラメータ比較の指定段への制限を、元の同じ単一パラメータ比較へ戻す。
方針：豊穣変換を元の段包含へ前合成し、全関手空間の指定順射の値まで照合する。
規約：成分での一致だけから coherent な関手同型の一致を推論しない。
使われ方：共同単位比較と以前の実面単位比較を、選択を変えずに接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
open EnrichedOrderedCylinder
variable {J : Type} [Preorder J] {D E : Jᵒᵖ ⥤ PointedSimplicialSet.{u}}

/-- 元の共同パラメータ変換の段制限は、元の同じ制限射の豊穣変換。 -/
lemma d3ParameterPre_stage (η : D ⟶ E) (i : J) :
    d3GradedOfEq (d3GradedPrecomp (stageInclusion (C := PointedKanObject.{u}) i)
      (d3ParameterPre η)) (d3PointedKanParameterDiagram_stage E i)
        (d3PointedKanParameterDiagram_stage D i) = d3PointedKanPre (η.app (Opposite.op i)) := by
  apply d3Graded_ext
  intro X
  apply eq_of_heq
  apply HEq.trans (d3GradedOfEq_component_heq _ _ _ X)
  change HEq (StrictEnrichedTransformation.componentHom _ _ (d3ParameterPre η) ⟨i, X⟩)
    (StrictEnrichedTransformation.componentHom _ _ (d3PointedKanPre (η.app (Opposite.op i))) X)
  rw [d3ParameterPre_component, d3PointedKanPre_component]

/-- 段制限の始終点は、同じ内部 Hom 作用に厳密一致する。 -/
lemma d3ParameterDiagram_stage_map (D : Jᵒᵖ ⥤ PointedSimplicialSet.{u}) (i : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stageInclusion (C := PointedKanObject.{u}) i) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram D) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (D.obj (Opposite.op i))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, d3PointedKanParameterDiagram_stage]

/-- 元の共同比較を段で評価した関手同型は、同じ単一パラメータ比較そのもの。 -/
lemma d3ParameterPreFunctorIso_stage (η : D ≅ E) (i : J) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3ParameterPreFunctorIso η).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stageInclusion (C := PointedKanObject.{u}) i)))
      (d3ParameterDiagram_stage_map E i) (d3ParameterDiagram_stage_map D i) =
    d3PointedKanPreFunctorIso (η.hom.app (Opposite.op i)) := by
  apply Iso.ext
  apply eq_of_heq
  apply HEq.trans (d3FunctorIsoOfEq_hom_heq _ _ _)
  have hη : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (StrictEnrichedTransformation.componentHom _ _ (d3ParameterPre η.hom) X)).toTruncated := by
    intro X
    rw [d3ParameterPre_component]
    exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
      (d3PointedKanPre_piIsomorphism (η.hom.app (Opposite.op X.position)) X.val)
  have hp := d3GradedIso_precomp_hom_heq (stageInclusion (C := PointedKanObject.{u}) i)
    (d3ParameterPre η.hom) hη
  have hs := d3GradedHom_ofEq_heq
    (d3GradedPrecomp (stageInclusion (C := PointedKanObject.{u}) i) (d3ParameterPre η.hom))
    (d3PointedKanParameterDiagram_stage E i) (d3PointedKanParameterDiagram_stage D i)
  rw [d3ParameterPre_stage] at hs
  exact hp.trans hs.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
