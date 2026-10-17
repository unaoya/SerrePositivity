module
public import SerrePositivity.DifferentialGraded.Resolution.CanonicalZigzag
public import Mathlib.Data.ZMod.Basic

/-! # 反復列・最終解像度・任意解像度との準同値比較の監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

-- 元のHomのflatness・有界性を要求しない。
example (F : DGFunctor A D E) (hF : QuasiEquivalence F) :
    QuasiEquivalence (DGCategoryCellResolution.comparisonFunctor A D E F) :=
  DGCategoryCellResolution.comparisonFunctor_quasiEquivalence A D E F hF

-- 指定解像度のsourceはD/Eとは独立した宇宙zを持つ。
example (P : KFlatDGResolution.{u, v, z} A D) :
    P.comparisonRight.comp (KFlatDGResolution.canonical A D).augmentation =
      P.comparisonLeft.comp P.augmentation := P.comparison_augmentation

example (P : KFlatDGResolution.{u, v, z} A D) :
    QuasiEquivalence P.comparisonLeft ∧ QuasiEquivalence P.comparisonRight :=
  ⟨P.comparisonLeft_quasiEquivalence, P.comparisonRight_quasiEquivalence⟩

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (P : KFlatDGResolution.{0, v, z} (ZMod 2) D) : QuasiEquivalence P.comparisonRight :=
  P.comparisonRight_quasiEquivalence

-- Hom準同型からのH⁰完全忠実性は対象型のsmallnessを必要としない。
example (X : Type v) [DGCategory A X] (Y : Type w) [DGCategory A Y]
    (F : DGFunctor A X Y) (hF : HomQuasiIso F) :
    F.onHomotopy.Full ∧ F.onHomotopy.Faithful :=
  ⟨F.onHomotopy_full_of_homQuasiIso hF, F.onHomotopy_faithful_of_homQuasiIso hF⟩

namespace SerrePositivity.DifferentialGraded
#print axioms FixedObjectAugmentation.cellGenerator
#print axioms FixedObjectAugmentation.attach_map_cellGenerator
#print axioms FixedObjectAugmentation.Map.attachedHom_cellGenerator
#print axioms FixedObjectAugmentation.Map.comparisonThenAugmentation
#print axioms FixedObjectAugmentation.Map.augmentationThenFunctor
#print axioms FixedObjectAugmentation.Map.attachedFunctor_augmentation
#print axioms FixedObjectAugmentation.Map.attachedHom_augmentation
#print axioms FixedObjectAugmentation.Map.attach
#print axioms DGCategoryCellResolution.stageComparison
#print axioms DGCategoryCellResolution.transition_comparison
#print axioms DGCategoryCellResolution.comparisonCocone
#print axioms DGCategoryCellResolution.comparisonHom
#print axioms DGCategoryCellResolution.comparisonHom_augmentation
#print axioms DGCategoryCellResolution.comparisonHom_unit
#print axioms DGCategoryCellResolution.comparisonHom_comp
#print axioms DGCategoryCellResolution.comparison
#print axioms DGCategoryCellResolution.comparisonFunctor
#print axioms DGCategoryCellResolution.comparisonFunctor_augmentation
#print axioms DGCategoryCellResolution.comparisonHom_quasiIso
#print axioms DGCategoryCellResolution.comparisonFunctor_homQuasiIso
#print axioms DGFunctor.closedHomEquiv_map
#print axioms DGFunctor.homotopyHomologyEquiv_map_naturality
#print axioms DGFunctor.onHomotopy_map_bijective_of_homQuasiIso
#print axioms DGFunctor.onHomotopy_full_of_homQuasiIso
#print axioms DGFunctor.onHomotopy_faithful_of_homQuasiIso
#print axioms DGCategoryCellResolution.comparisonFunctor_essSurj
#print axioms DGCategoryCellResolution.comparisonFunctor_quasiEquivalence
#print axioms KFlatDGResolution.ComparisonSource
#print axioms KFlatDGResolution.comparisonLeft
#print axioms KFlatDGResolution.comparisonRight
#print axioms KFlatDGResolution.comparisonLeft_quasiEquivalence
#print axioms KFlatDGResolution.comparisonRight_quasiEquivalence
#print axioms KFlatDGResolution.comparisonSource_homKFlat
#print axioms KFlatDGResolution.comparison_augmentation
end SerrePositivity.DifferentialGraded
