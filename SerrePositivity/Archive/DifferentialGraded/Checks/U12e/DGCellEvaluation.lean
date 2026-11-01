module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Path
public import Mathlib.Data.ZMod.Basic

/-! # 全Hom評価・cell付加へのdg関手延長・次段のcell充填の監査

## 概要
全Hom評価・cell付加へのdg関手延長・次段のcell充填の監査。

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
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)
  (E : Type z) [DGCategory A E] (F : DGFunctor A D E)
  (P : Family.PrimitiveData A D I C E F)

-- 任意可換環、独立宇宙、Homのflatness・Dのsmallness仮定なし。
example : DGFunctor A (C.Objects A D I) E := P.extension

example (x y : D) : C.attachedHom A D I x y ⟶ homObject A E (F.obj x) (F.obj y) :=
  P.attachedEvaluation x y

example : (C.embedding A D I).comp P.extension = F := P.embedding_comp_extension

example (i : I) :
    (P.extension.map (⟨C.source i⟩ : C.Objects A D I) ⟨C.target i⟩).f (C.degree i)
      (C.generatorElement A D I i) = P.primitive i := P.extension_generator i

example [Small.{u} D] :
    DGFunctor A ((boundaryFamily A D E F).Objects A D (DGCategoryBoundaryCells.Index A D E F)) E :=
  DGCategoryBoundaryCells.attachedAugmentation A D E F

example [Small.{u} D] (x y : D) (c : ComplexBoundaryCell A (F.map x y)) :
    ∃ t : ((boundaryFamily A D E F).attachedHom A D (DGCategoryBoundaryCells.Index A D E F) x y).X
        c.degree,
      ((boundaryFamily A D E F).attachedHom A D (DGCategoryBoundaryCells.Index A D E F) x y).d
        c.degree (c.degree + 1) t =
        ((boundaryFamily A D E F).originalHomInclusion A D
          (DGCategoryBoundaryCells.Index A D E F) x y).f (c.degree + 1) c.cycle.val ∧
      ((DGCategoryBoundaryCells.attachedAugmentation A D E F).map ⟨x⟩ ⟨y⟩).f
        c.degree t = c.primitive :=
  DGCategoryBoundaryCells.attachedAugmentation_fills A D E F x y c

example (D : Type v) [DGCategory (ZMod 2) D] (I : Type w) [Small.{0} I]
    (C : Family (ZMod 2) D I) (E : Type z) [DGCategory (ZMod 2) E]
    (F : DGFunctor (ZMod 2) D E) (P : Family.PrimitiveData (ZMod 2) D I C E F) :
    DGFunctor (ZMod 2) (C.Objects (ZMod 2) D I) E := P.extension

namespace SerrePositivity.DifferentialGraded
#print axioms DGCellAttachment.Family.pathCochainDesc
#print axioms DGCellAttachment.Family.pathCochainDesc_precomp
#print axioms DGCellAttachment.Family.pathCochainDesc_unique
#print axioms DGCellAttachment.Family.PrimitiveData.internalEvaluation
#print axioms DGCellAttachment.Family.PrimitiveData.internalEvaluation_precomp
#print axioms DGCellAttachment.Family.PrimitiveData.internalEvaluation_original
#print axioms DGCellAttachment.Family.PrimitiveData.internalEvaluation_generator
#print axioms DGCellAttachment.Family.PrimitiveData.pathEvaluation_prepend
#print axioms DGCellAttachment.Family.PrimitiveData.primitiveAction
#print axioms DGCellAttachment.Family.PrimitiveData.boundaryOriginalAction
#print axioms DGCellAttachment.Family.PrimitiveData.primitiveAction_differential
#print axioms DGCellAttachment.Family.PrimitiveData.primitiveAction_evaluate
#print axioms DGCellAttachment.Family.PrimitiveData.boundaryAction_pathEvaluation
#print axioms DGCellAttachment.Family.PrimitiveData.evaluationOriginalAction
#print axioms DGCellAttachment.Family.PrimitiveData.evaluationPrefixAction
#print axioms DGCellAttachment.Family.PrimitiveData.evaluationPrefixAction_differential
#print axioms DGCellAttachment.Family.PrimitiveData.pathEvaluation_cons_action
#print axioms DGCellAttachment.Family.PrimitiveData.evaluationPrefix_boundary
#print axioms DGCellAttachment.Family.PrimitiveData.pathEvaluationTail
#print axioms DGCellAttachment.Family.PrimitiveData.pathEvaluation_cons_differential
#print axioms DGCellAttachment.Family.PrimitiveData.internalEvaluation_prefixPath
#print axioms DGCellAttachment.Family.PrimitiveData.pathEvaluationTail_internalEvaluation
#print axioms DGCellAttachment.Family.PrimitiveData.pathEvaluation_differential
#print axioms DGCellAttachment.Family.PrimitiveData.internalEvaluation_differential
#print axioms DGCellAttachment.Family.PrimitiveData.attachedEvaluation
#print axioms DGCellAttachment.Family.PrimitiveData.attachedEvaluation_f
#print axioms DGCellAttachment.Family.PrimitiveData.attachedEvaluation_original
#print axioms DGCellAttachment.Family.PrimitiveData.attachedEvaluation_generator
#print axioms DGCellAttachment.Family.PrimitiveData.attachedEvaluation_path
#print axioms DGCellAttachment.Family.PrimitiveData.attachedEvaluation_unit
#print axioms DGCellAttachment.Family.PrimitiveData.pathEvaluation_append
#print axioms DGCellAttachment.Family.tensorTwoPathCochain_ext
#print axioms DGCellAttachment.Family.PrimitiveData.internalEvaluation_composition
#print axioms DGCellAttachment.Family.PrimitiveData.attachedEvaluation_composition
#print axioms DGCellAttachment.Family.PrimitiveData.extension
#print axioms DGCellAttachment.Family.PrimitiveData.embedding_comp_extension
#print axioms DGCellAttachment.Family.PrimitiveData.extension_generator
#print axioms DGCategoryBoundaryCells.attachedAugmentation
#print axioms DGCategoryBoundaryCells.embedding_comp_attachedAugmentation
#print axioms DGCategoryBoundaryCells.attachedAugmentation_fills
end SerrePositivity.DifferentialGraded
