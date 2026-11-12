module
public import SerrePositivity.KST.SConstruction.CoherentOrdinaryPrismSlices
public import SerrePositivity.KST.SConstruction.KPrismNativeStringFamilies

/-! # 元の K prism の上下の図式と頂点の照合
概要：通常積圏表示の下段・上段を、元の suspension と次段の strict な図式へ同定する。
方針：同じ元の円柱の端点等式と、段の coherent 図式の厳密な包含比較を用いる。
規約：全段・全単体と元の点つき K 対象を保持する。
使われ方：上下の native Hom の二円柱を元の二合成へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismSliceDiagrams_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 下段の全入力図式は、元の段の suspension の strict な図式そのもの。 -/
lemma kKanOriginalPrismStringDiagram_bottom {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (coherentPrismSliceFunctor I (ULift.up 0))) ≫
        kKanOriginalPrismStringDiagram r F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram ((F ⋙ kKanSequenceLevelFunctor r) ⋙
        MonoidalCategory.tensorLeft PointedSimplicialSet.circle.{u}) := by
  rw [kKanOriginalPrismStringDiagram, coherentOrdinaryPrismSlice_source]
  change (kKanCoherentLevelDiagram F r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor = _
  rw [kKanCoherentLevelDiagram_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.strictCoherentDiagram_postcomp,
    suspensionEnrichedUnderlying_eq]

/-- 上段の全入力図式は、元の次段の strict な図式そのもの。 -/
lemma kKanOriginalPrismStringDiagram_top {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (coherentPrismSliceFunctor I (ULift.up 1))) ≫
        kKanOriginalPrismStringDiagram r F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ kKanSequenceLevelFunctor (r + 1)) := by
  rw [kKanOriginalPrismStringDiagram, coherentOrdinaryPrismSlice_target,
    kKanCoherentLevelDiagram_inclusion]

/-- 下段の元の頂点は、元の K の段の suspension そのもの。 -/
lemma kKanOriginalPrismStringVertex_bottom {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (i, ULift.up 0) =
      PointedSimplicialSet.circle.{u} ⊗ ((kKanSequence (F.obj i)).level r).space := by
  have h := congrArg (fun Q => coherentStringVertexObject Q i)
    (kKanOriginalPrismStringDiagram_bottom r F)
  rw [coherentStringVertexObject_precomp] at h
  change coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (i, ULift.up 0) =
    PointedSimplicialSet.circle.{u} ⊗ (kKanSequenceLevelFunctor r).obj (F.obj i) at h
  exact h.trans (congrArg (PointedSimplicialSet.circle.{u} ⊗ ·)
    (kKanSequenceLevelFunctor_obj r (F.obj i)))

/-- 上段の元の頂点は、元の K の次段そのもの。 -/
lemma kKanOriginalPrismStringVertex_top {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (i, ULift.up 1) =
      ((kKanSequence (F.obj i)).level (r + 1)).space := by
  have h := congrArg (fun Q => coherentStringVertexObject Q i)
    (kKanOriginalPrismStringDiagram_top r F)
  rw [coherentStringVertexObject_precomp] at h
  change coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (i, ULift.up 1) =
    (kKanSequenceLevelFunctor (r + 1)).obj (F.obj i) at h
  exact h.trans (kKanSequenceLevelFunctor_obj (r + 1) (F.obj i))

end SerrePositivity.KST.SConstruction
