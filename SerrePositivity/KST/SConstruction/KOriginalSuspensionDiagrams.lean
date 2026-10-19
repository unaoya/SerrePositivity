module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblySuspensionSquares
public import SerrePositivity.KST.SConstruction.KNativeOmegaDiagrams

/-! # 零段を含む元の K の全段の suspension 円柱
概要：元の K 空間を零段に保ち、元の全構造射を成分に持つ全入力円柱を全段で与える。
方針：零段には smash/loop 随伴の元の余単位、正の段には補正済みの全入力円柱を使う。
規約：段の対象と構造射は元の Kan 列のものを厳密に回収する。
使われ方：全段の指定構造射を保持する BF の coherent な関手化の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial
local instance kOriginalSuspension_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の K の段の図式を包含して忘れると、全単体で元の通常の図式を回収する。 -/
lemma kKanCoherentLevelDiagram_inclusion {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (r : ℕ) :
    kKanCoherentLevelDiagram F r ≫ coherentNerveMap pointedKanInclusionEnriched =
      strictCoherentDiagram (F ⋙ kKanSequenceLevelFunctor r) :=
  pointedKanInclusion_coherentDiagram (F ⋙ kKanSequenceLevelFunctor r)
    (fun i => kKanSequenceLevelFunctor_kanComplex r (F.obj i))

/-- 元の零段 K 空間の suspension から第一段への、余単位の strict な自然変換。 -/
def kKanZeroSuspensionTransformation {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) :
    (F ⋙ kKanSequenceLevelFunctor 0) ⋙
      MonoidalCategory.tensorLeft PointedSimplicialSet.circle.{u} ⟶
        F ⋙ kKanSequenceLevelFunctor 1 where
  app i := (suspensionLoopEquiv _ _).symm (𝟙 (boundaryKSpaceFunctor.obj (F.obj i)))
  naturality _ _ f :=
    pointedLoopCounit_naturality ((boundaryKanRealizationFunctor 0).map (F.map f))

/-- 余単位の成分は、元の Kan 列の零段構造射そのもの。 -/
lemma kKanZeroSuspensionTransformation_app {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (i : I) :
    (kKanZeroSuspensionTransformation F).app i = (kKanSequence (F.obj i)).sigma 0 := rfl

/-- 元の零段を保持した全入力の suspension 比較円柱。 -/
def kKanZeroSuspensionHomotopy {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) : SSet.Homotopy
      (kKanCoherentLevelDiagram F 0 ≫ coherentNerveMap pointedKanInclusionEnriched ≫
        coherentNerveMap suspensionEnrichedFunctor)
      (kKanCoherentLevelDiagram F 1 ≫ coherentNerveMap pointedKanInclusionEnriched) := by
  let H := StrictDiagramTransformation.homotopy (kKanZeroSuspensionTransformation F)
  have hs : kKanCoherentLevelDiagram F 0 ≫ coherentNerveMap pointedKanInclusionEnriched ≫
      coherentNerveMap suspensionEnrichedFunctor =
    strictCoherentDiagram ((F ⋙ kKanSequenceLevelFunctor 0) ⋙
      MonoidalCategory.tensorLeft PointedSimplicialSet.circle.{u}) := by
    change (pointedKanCoherentDiagram (F ⋙ kKanSequenceLevelFunctor 0) _ ≫
      coherentNerveMap pointedKanInclusionEnriched) ≫
        coherentNerveMap suspensionEnrichedFunctor = _
    rw [pointedKanInclusion_coherentDiagram, strictCoherentDiagram_postcomp,
      suspensionEnrichedUnderlying_eq]
  have ht : kKanCoherentLevelDiagram F 1 ≫ coherentNerveMap pointedKanInclusionEnriched =
      strictCoherentDiagram (F ⋙ kKanSequenceLevelFunctor 1) :=
    pointedKanInclusion_coherentDiagram (F ⋙ kKanSequenceLevelFunctor 1) _
  refine { h := H.h, h₀ := H.h₀.trans hs.symm, h₁ := H.h₁.trans ht.symm, rel := ?_ }
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact False.elim x.1.property

/-- 零段の全入力円柱は、元の零段構造射の辺を全対象で厳密に回収する。 -/
lemma kKanZeroSuspensionHomotopy_vertex_edge {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (i : I) :
    (simplicialHomotopyVertexEdge (kKanZeroSuspensionHomotopy F)
      (ULift.up (nerveVertex i))).edge =
      (coherentNerveEdge ((kKanSequence (F.obj i)).sigma 0)).edge := by
  have h := StrictDiagramTransformation.component_edge (kKanZeroSuspensionTransformation F) i
  rw [kKanZeroSuspensionTransformation_app] at h
  exact h

/-- 元の零段と全段の図式について、元の固定構造射を成分に持つ suspension 円柱。 -/
def kKanOriginalSuspensionHomotopy {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (r : ℕ) : SSet.Homotopy
      (kKanCoherentLevelDiagram F r ≫ coherentNerveMap pointedKanInclusionEnriched ≫
        coherentNerveMap suspensionEnrichedFunctor)
      (kKanCoherentLevelDiagram F (r + 1) ≫ coherentNerveMap pointedKanInclusionEnriched) :=
  match r with
  | 0 => kKanZeroSuspensionHomotopy F
  | r + 1 => boundaryAssemblyOriginalSuspensionHomotopy r F

/-- 全段の全入力円柱は、元の K の Kan 列の構造射の辺を厳密に回収する。 -/
lemma kKanOriginalSuspensionHomotopy_vertex_edge {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) (r : ℕ) (i : I) :
    (simplicialHomotopyVertexEdge (kKanOriginalSuspensionHomotopy F r)
      (ULift.up (nerveVertex i))).edge =
      (coherentNerveEdge ((kKanSequence (F.obj i)).sigma r)).edge := by
  cases r with
  | zero => exact kKanZeroSuspensionHomotopy_vertex_edge F i
  | succ r => exact boundaryAssemblyOriginalSuspensionHomotopy_vertex_edge r F i

end SerrePositivity.KST.SConstruction
