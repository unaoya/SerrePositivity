module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObject
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import Mathlib.Data.ZMod.Basic

/-! # 任意次数cell延長の一意性と解像度比較の入口の検証

## 概要
任意次数cell延長の一意性と解像度比較の入口の検証。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : DGCellAttachment.Family A D I)
  (E : Type z) [DGCategory A E]

-- 元の対象型やtargetのsmallness、Homのflatness・有界性を要求しない。
example (G : DGFunctor A (C.Objects A D I) E) :
    (C.restrictPrimitives A D I G).extension = G := C.extension_restrict A D I G

example [Small.{u} D] [Small.{u} E] (F : DGFunctor A D E) :
    FixedObjectAugmentation.Map (DGCategoryCellResolution.initial A D)
      (DGCategoryCellResolution.initial A E) F :=
  DGCategoryCellResolution.initialComparison A D E F

example (D E : Type v) [DGCategory (ZMod 2) D] [DGCategory (ZMod 2) E]
    [Small.{0} D] [Small.{0} E] (F : DGFunctor (ZMod 2) D E) :
    FixedObjectAugmentation.Map (DGCategoryCellResolution.initial (ZMod 2) D)
      (DGCategoryCellResolution.initial (ZMod 2) E) F :=
  DGCategoryCellResolution.initialComparison (ZMod 2) D E F

namespace SerrePositivity.DifferentialGraded
#print axioms tensorSandwich_append_distinct
#print axioms sphere_generator_span
#print axioms sphereMiddleCochain_ext₀
#print axioms DGCellAttachment.Family.generatorTerm_append
#print axioms DGCellAttachment.Family.prependMap_generatorTerm_append
#print axioms DGCellAttachment.Family.generator_internalComposition_inclusion
#print axioms DGCellAttachment.Family.prefixPath_generated
#print axioms DGCellAttachment.Family.prefixPath_generator
#print axioms DGCellAttachment.Family.path_inclusion_generator
#print axioms DGCellAttachment.Family.restrictFunctor
#print axioms DGCellAttachment.Family.restrictPrimitives
#print axioms DGCellAttachment.Family.restrictionHomCochain
#print axioms DGCellAttachment.Family.restrictionHomCochain_path
#print axioms DGCellAttachment.Family.restrictionHomCochain_eq_internalEvaluation
#print axioms DGCellAttachment.Family.extension_restrict
#print axioms DGCellAttachment.Family.PrimitiveData.hext
#print axioms DGCellAttachment.Family.PrimitiveData.extension_congr
#print axioms DGCellAttachment.Family.extension_unique
#print axioms DGCellAttachment.Family.functor_ext
#print axioms complexMapCycle
#print axioms complexMapCycle_id
#print axioms complexMapCycle_comp
#print axioms complexSphereMap_mapCycle
#print axioms complexCycleCoverMap
#print axioms complexCycleCoverLift_map
#print axioms complexCycleCoverMap_π
#print axioms complexCycleCoverMap_id
#print axioms complexCycleCoverMap_comp
#print axioms DGCategoryCycleCover.map
#print axioms DGCategoryCycleCover.map_obj
#print axioms DGCategoryCycleCover.edge_map
#print axioms DGCategoryCycleCover.map_augmentation
#print axioms FixedObjectAugmentation.Map
#print axioms FixedObjectAugmentation.Map.toDGFunctor
#print axioms FixedObjectAugmentation.Map.cellMap
#print axioms FixedObjectAugmentation.Map.cellMap_degree
#print axioms FixedObjectAugmentation.Map.cellMap_primitive
#print axioms FixedObjectAugmentation.Map.baseExtension
#print axioms FixedObjectAugmentation.Map.extensionPrimitives
#print axioms FixedObjectAugmentation.Map.attachedFunctor
#print axioms FixedObjectAugmentation.Map.attachedHom
#print axioms FixedObjectAugmentation.Map.transition_attachedHom
#print axioms FixedObjectAugmentation.Map.attachedHom_id
#print axioms FixedObjectAugmentation.Map.attachedHom_comp
#print axioms DGFunctor.hcongr_map
#print axioms DGCategoryCellResolution.initialComparison
end SerrePositivity.DifferentialGraded
