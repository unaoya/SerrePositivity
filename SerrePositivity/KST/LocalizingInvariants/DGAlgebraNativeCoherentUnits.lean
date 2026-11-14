module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeOrdinaryHomKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KanDiagramBundle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentUnderlyingHo
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexRestriction

/-!
概要：実 frame の元の単位を、全標的の coherent 図式間の射として保持する。
方針：既存の Kan 図式束縛・通常射の coherent 実現・ホモトピー圏の関手を合成する。
規約：対象別の射の等式で全図式の自然性を代用しない。
使われ方：指定局所化比較の二胞体と元の零単体の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

/-- 元の提示上の全 Kan 図式を、同じ全図式関手空間のホモトピー圏へ実現する。 -/
def nativeKanDiagramRealizationFunctor :
    (InfinityPresentation R ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1}) ⥤
      hoFunctor.obj ((ihom ((SSet.uliftFunctor.{u + 2, u + 1}).obj
        (nerve (InfinityPresentation R)))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 1}) :=
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanDiagramBundle ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentUnderlyingHoFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject (InfinityPresentation R)) ⋙
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization (InfinityPresentation R))).toFunctor
  F.copyObj (fun D => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve D)))
    (fun D => eqToIso (congrArg HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization_vertex ⟨D, trivial⟩)))

lemma nativeKanDiagramRealizationFunctor_map
    {F G : InfinityPresentation R ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1}} (η : F ⟶ G) :
    (nativeKanDiagramRealizationFunctor R).map η =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge
          (F := ⟨F, trivial⟩) (G := ⟨G, trivial⟩)
          (Functor.whiskerRight η _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).toTruncated := by
  change _ = Truncated.HomotopyCategory.homMk
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom (Functor.whiskerRight η _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization (InfinityPresentation R))).ofEq
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization_vertex ⟨F, trivial⟩)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization_vertex ⟨G, trivial⟩)).toTruncated
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homMk_edge_ofEq]
  rfl

/-- 元の全標的自然変換を、同じ ULiftHom 提示の Kan 値自然変換として保持する。 -/
def nativePresentationKanTransformation
    {F G : Mon (Complex R) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1}}
    (η : F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :
    (ULiftHom.down : InfinityPresentation R ⥤ _) ⋙ F ⟶
      (ULiftHom.down : InfinityPresentation R ⥤ _) ⋙ G where
  app B := η.app B.objDown
  naturality _B _C f := η.naturality f.down

lemma nativeMixedPresentationIso_hom
    (F G : Mon (Complex R) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1})
    (η : F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (hη : ∀ B, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.obj B).obj) (Y := (G.obj B).obj) (η.app B)) :
    (nativeMixedPresentationIso R F G η hη).hom =
      (nativeKanDiagramRealizationFunctor R).map (nativePresentationKanTransformation R η) := by
  rw [nativeKanDiagramRealizationFunctor_map]
  rfl

variable (A : Mon (Complex R))

def nativeCellMappingCoherentUnit :
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellOrdinaryInfinityKanFunctor R A))) ⟶
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (multiplicativeCellMappingInfinityCoherent R A)) :=
  (nativeKanDiagramRealizationFunctor R).map
    (nativePresentationKanTransformation R (nativeCellMappingUnitLarge R A))

def nativeCellSourceFrameMappingCoherentUnit :
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellOrdinaryInfinityKanFunctor R A))) ⟶
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellSourceFrameInfinityKanFunctor R A))) :=
  (nativeKanDiagramRealizationFunctor R).map
    (nativePresentationKanTransformation R (nativeCellSourceFrameMappingUnitLarge R A))

def nativeCellChosenRightMappingCoherentUnit :
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellOrdinaryInfinityKanFunctor R A))) ⟶
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))) :=
  (nativeKanDiagramRealizationFunctor R).map
    (nativePresentationKanTransformation R (nativeCellChosenRightMappingUnitLarge R A))

set_option maxHeartbeats 800000 in
-- 実モデルの全標的図式の射を同じ合成へ正規化する局所予算。
lemma nativeCellMappingCoherentUnit_mixed_triangle :
    nativeCellSourceFrameMappingCoherentUnit R A ≫ (nativeCellMixedLeftCoherentIso R A).hom =
      nativeCellMappingCoherentUnit R A ≫ (nativeCellMixedRightCoherentIso R A).hom := by
  unfold nativeCellSourceFrameMappingCoherentUnit nativeCellMappingCoherentUnit
    nativeCellMixedLeftCoherentIso nativeCellMixedRightCoherentIso
  rw [nativeMixedPresentationIso_hom, nativeMixedPresentationIso_hom]
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

lemma nativeCellChosenRightMappingCoherentUnit_mixed_triangle :
    nativeCellSourceFrameMappingCoherentUnit R A ≫
        (nativeCellChosenMixedLeftCoherentIso R A).hom =
      nativeCellChosenRightMappingCoherentUnit R A ≫
        (nativeCellChosenMixedRightCoherentIso R A).hom := by
  unfold nativeCellSourceFrameMappingCoherentUnit nativeCellChosenRightMappingCoherentUnit
    nativeCellChosenMixedLeftCoherentIso nativeCellChosenMixedRightCoherentIso
  rw [nativeMixedPresentationIso_hom, nativeMixedPresentationIso_hom]
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

lemma nativeCellMappingCoherentUnit_sourceFrame :
    nativeCellMappingCoherentUnit R A ≫
        (multiplicativeCellMappingSourceFrameCoherentIso R A).hom =
      nativeCellSourceFrameMappingCoherentUnit R A := by
  change nativeCellMappingCoherentUnit R A ≫
      ((nativeCellMixedRightCoherentIso R A).hom ≫
        (nativeCellMixedLeftCoherentIso R A).inv) = _
  rw [← Category.assoc, ← nativeCellMappingCoherentUnit_mixed_triangle,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma nativeCellChosenRightMappingCoherentUnit_sourceFrame :
    nativeCellChosenRightMappingCoherentUnit R A ≫
        (nativeCellChosenMappingSourceFrameCoherentIso R A).hom =
      nativeCellSourceFrameMappingCoherentUnit R A := by
  change nativeCellChosenRightMappingCoherentUnit R A ≫
      ((nativeCellChosenMixedRightCoherentIso R A).hom ≫
        (nativeCellChosenMixedLeftCoherentIso R A).inv) = _
  rw [← Category.assoc, ← nativeCellChosenRightMappingCoherentUnit_mixed_triangle,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 実 AW と選んだ right frame の全標的同型は、元の全射の単位を保持する。 -/
lemma nativeCellMappingCoherentUnit_chosenRight :
    nativeCellMappingCoherentUnit R A ≫
        (multiplicativeCellMappingChosenRightCoherentIso R A).hom =
      nativeCellChosenRightMappingCoherentUnit R A := by
  change nativeCellMappingCoherentUnit R A ≫
      ((multiplicativeCellMappingSourceFrameCoherentIso R A).hom ≫
        (nativeCellChosenMappingSourceFrameCoherentIso R A).inv) = _
  rw [← Category.assoc, nativeCellMappingCoherentUnit_sourceFrame,
    ← nativeCellChosenRightMappingCoherentUnit_sourceFrame, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
