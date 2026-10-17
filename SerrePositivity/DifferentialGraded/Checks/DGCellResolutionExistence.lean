module
public import SerrePositivity.DifferentialGraded.Resolution.CellCategory
public import SerrePositivity.DifferentialGraded.Resolution.Bimodule
public import Mathlib.Data.ZMod.Basic

/-! # 任意の小さいdg圏のK-flat解像度：反復列・豊穣構造・準同値・一般存在の監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

-- 元のHomのK-flat性、有界性、次数ごとのflatnessを仮定しない。
example : Nonempty (KFlatDGResolution.{u, v, v} A D) := KFlatDGResolution.nonempty A D

example : DGFunctor A (KFlatDGResolution.canonical A D).source D :=
  (KFlatDGResolution.canonical A D).augmentation

example : QuasiEquivalence (KFlatDGResolution.canonical A D).augmentation :=
  (KFlatDGResolution.canonical A D).quasiEquivalence

example : localHomKFlat A (KFlatDGResolution.canonical A D).source :=
  (KFlatDGResolution.canonical A D).homKFlat

example (x y : D) : QuasiIso (DGCategoryCellResolution.candidateAugmentation A D x y) :=
  DGCategoryCellResolution.candidateAugmentation_quasiIso A D x y

-- 一般の固定対象増大ではtarget対象宇宙も独立。targetのsmallnessは不要。
example (X : Type v) [Small.{u} X] (E : Type w) [DGCategory A E] (o : X → E)
    (S : FixedObjectAugmentation A X E o) (hS : S.HomKFlat) : S.attach.HomKFlat :=
  S.attach_homKFlat hS

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D] :
    Nonempty (KFlatDGResolution.{0, v, v} (ZMod 2) D) := KFlatDGResolution.nonempty (ZMod 2) D

-- 既存の指定解像度上の導来合成へ、元のHomの局所K-flat仮定なしで入力できる。
example (B : Type v) [DGCategory A B] [Small.{u} B]
    (C : Type w) [DGCategory A C] [Small.{u} C]
    (E : Type z) [DGCategory A E] [Small.{u} E] :
    ResolutionBimodule.DerivedCategory A (KFlatDGResolution.canonical A C)
      (KFlatDGResolution.canonical A E) ⥤
      (ResolutionBimodule.DerivedCategory A (KFlatDGResolution.canonical A B)
        (KFlatDGResolution.canonical A C) ⥤
        ResolutionBimodule.DerivedCategory A (KFlatDGResolution.canonical A B)
          (KFlatDGResolution.canonical A E)) :=
  ResolutionBimodule.composeFunctor A (KFlatDGResolution.canonical A B)
    (KFlatDGResolution.canonical A C) (KFlatDGResolution.canonical A E)

namespace SerrePositivity.DifferentialGraded
#print axioms FixedObjectAugmentation
#print axioms FixedObjectAugmentation.toDGFunctor
#print axioms FixedObjectAugmentation.CellIndex
#print axioms FixedObjectAugmentation.cellIndexSmall
#print axioms FixedObjectAugmentation.cells
#print axioms FixedObjectAugmentation.cellPrimitives
#print axioms FixedObjectAugmentation.attachedCategory
#print axioms FixedObjectAugmentation.attach
#print axioms FixedObjectAugmentation.transition
#print axioms FixedObjectAugmentation.transition_id
#print axioms FixedObjectAugmentation.transition_comp
#print axioms FixedObjectAugmentation.transition_augmentation
#print axioms FixedObjectAugmentation.attach_fills
#print axioms FixedObjectAugmentation.HomKFlat
#print axioms FixedObjectAugmentation.attach_homKFlat
#print axioms DGCategoryCellResolution.initial
#print axioms DGCategoryCellResolution.initial_homKFlat
#print axioms DGCategoryCellResolution.stage
#print axioms DGCategoryCellResolution.stage_homKFlat
#print axioms DGCategoryCellResolution.stageHom
#print axioms DGCategoryCellResolution.transition
#print axioms DGCategoryCellResolution.stageAugmentation
#print axioms DGCategoryCellResolution.transition_augmentation
#print axioms DGCategoryCellResolution.homDiagram
#print axioms DGCategoryCellResolution.augmentationCocone
#print axioms DGCategoryCellResolution.stage_fills
#print axioms DGCategoryCellResolution.candidateHom
#print axioms DGCategoryCellResolution.candidateAugmentation
#print axioms DGCategoryCellResolution.stageInclusion
#print axioms DGCategoryCellResolution.candidateAugmentation_quasiIso
#print axioms DGCategoryCellResolution.candidateHom_kFlat
#print axioms DGCategoryCellResolution.candidateTensorIsColimit
#print axioms DGCategoryCellResolution.compositionCocone
#print axioms DGCategoryCellResolution.candidateComposition
#print axioms DGCategoryCellResolution.candidateComposition_stage
#print axioms DGCategoryCellResolution.candidateComposition_apply_stage
#print axioms DGCategoryCellResolution.candidateUnit
#print axioms DGCategoryCellResolution.candidateUnit_stage
#print axioms DGCategoryCellResolution.candidateUnit_augmentation
#print axioms DGCategoryCellResolution.candidateComposition_augmentation
#print axioms DGCategoryCellResolution.candidateComposition_left_unit
#print axioms DGCategoryCellResolution.candidateComposition_right_unit
#print axioms DGCategoryCellResolution.stageComposition_assoc
#print axioms DGCategoryCellResolution.candidateTripleIsColimit
#print axioms DGCategoryCellResolution.candidateComposition_assoc
#print axioms FixedObjectAugmentation.Objects
#print axioms FixedObjectAugmentation.objectEquiv
#print axioms FixedObjectAugmentation.objectsSmall
#print axioms FixedObjectAugmentation.objectsDGCategory
#print axioms FixedObjectAugmentation.augmentation
#print axioms FixedObjectAugmentation.objects_homKFlat
#print axioms DGCategoryCellResolution.candidate
#print axioms DGCategoryCellResolution.Source
#print axioms DGCategoryCellResolution.augmentation
#print axioms DGCategoryCellResolution.source_homKFlat
#print axioms DGCategoryCellResolution.augmentation_homQuasiIso
#print axioms DGCategoryCellResolution.augmentation_essSurj
#print axioms DGCategoryCellResolution.augmentation_quasiEquivalence
#print axioms DGCategoryCellResolution.resolution
#print axioms KFlatDGResolution.canonical
#print axioms KFlatDGResolution.nonempty
#print axioms DGCategoryCellResolution.stageInclusion_augmentation
#print axioms DGCategoryCellResolution.transition_inclusion
end SerrePositivity.DifferentialGraded
