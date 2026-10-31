module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.LengthColimit
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Augmentation
public import Mathlib.Data.ZMod.Basic

/-! # 任意次数cell付加のpath長filtration・分裂・最終K-flat性の監査

## 概要
任意次数cell付加のpath長filtration・分裂・最終K-flat性の監査。

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
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

example (hD : localHomKFlat A D) : localHomKFlat A (C.Objects A D I) :=
  C.attachedDGCategory_localHomKFlat A D I hD

example (hD : localHomKFlat A D) (x y : D) :
    complexKFlat A (C.attachedHom A D I x y) := C.attachedHom_kFlat A D I hD x y

example (n : ℕ) (x y : D) (i : ℤ) :
    ((C.lengthShortComplex A D I n x y).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)).Splitting :=
  C.lengthSplitting A D I n x y i

example (x y : D) : IsColimit (C.lengthCocone A D I x y) := C.lengthIsColimit A D I x y

example [Small.{u} D] (hD : localHomKFlat A D) (E : Type z) [DGCategory A E]
    (F : DGFunctor A D E) :
    localHomKFlat A ((boundaryFamily A D E F).Objects A D
      (DGCategoryBoundaryCells.Index A D E F)) :=
  (boundaryFamily A D E F).attachedDGCategory_localHomKFlat A D
    (DGCategoryBoundaryCells.Index A D E F) hD

-- 標数2・非有界・独立宇宙。Dの対象smallnessは一般のcell付加には不要。
example (D : Type v) [DGCategory (ZMod 2) D] (I : Type w) [Small.{0} I]
    (C : Family (ZMod 2) D I) (hD : localHomKFlat (ZMod 2) D) :
    localHomKFlat (ZMod 2) (C.Objects (ZMod 2) D I) :=
  C.attachedDGCategory_localHomKFlat (ZMod 2) D I hD

namespace SerrePositivity.DifferentialGraded
#print axioms ComplexCoproduct.cochain_ext
#print axioms ComplexCoproduct.cochainDesc
#print axioms ComplexCoproduct.cochainDesc_precomp
#print axioms ComplexCoproduct.subfamily
#print axioms ComplexCoproduct.inclusion
#print axioms ComplexCoproduct.ι_inclusion
#print axioms ComplexCoproduct.projection
#print axioms ComplexCoproduct.ι_projection_mem
#print axioms ComplexCoproduct.ι_projection_not_mem
#print axioms ComplexCoproduct.inclusion_projection
#print axioms ComplexCoproduct.inclusion_splitMono
#print axioms ComplexCoproduct.select
#print axioms ComplexCoproduct.ι_select_mem
#print axioms ComplexCoproduct.ι_select_not_mem
#print axioms ComplexCoproduct.select_self
#print axioms ComplexCoproduct.select_inclusion
#print axioms ComplexCoproduct.select_comp
#print axioms ComplexCoproduct.select_zero
#print axioms ComplexCoproduct.select_partition
#print axioms cochain_postcomp_injective_of_retraction
#print axioms perturbation_closed_of_inclusion
#print axioms perturbation_square_zero_of_inclusion
#print axioms perturbMap
#print axioms perturbMap_f
#print axioms DGCellAttachment.Family.lengthSet
#print axioms DGCellAttachment.Family.lengthInternalHom
#print axioms DGCellAttachment.Family.lengthInclusion
#print axioms DGCellAttachment.Family.lengthProjection
#print axioms DGCellAttachment.Family.lengthInclusion_projection
#print axioms DGCellAttachment.Family.lengthReplacement
#print axioms DGCellAttachment.Family.replaceSummand_length_projection_inclusion
#print axioms DGCellAttachment.Family.replaceRow_length_projection_inclusion
#print axioms DGCellAttachment.Family.lengthReplacement_inclusion
#print axioms DGCellAttachment.Family.lengthReplacement_closed
#print axioms DGCellAttachment.Family.lengthReplacement_square_zero
#print axioms DGCellAttachment.Family.lengthHom
#print axioms DGCellAttachment.Family.lengthHom_d
#print axioms DGCellAttachment.Family.lengthHomInclusion
#print axioms DGCellAttachment.Family.lengthHomInclusion_f
#print axioms DGCellAttachment.Family.lengthHomInclusion_degreewiseMono
#print axioms DGCellAttachment.Family.lengthHomInclusion_mono
#print axioms DGCellAttachment.Family.lengthInternalMap
#print axioms DGCellAttachment.Family.lengthInternalMap_inclusion
#print axioms DGCellAttachment.Family.lengthInternalMap_replacement
#print axioms DGCellAttachment.Family.lengthMap
#print axioms DGCellAttachment.Family.lengthMap_f
#print axioms DGCellAttachment.Family.lengthMap_inclusion
#print axioms DGCellAttachment.Family.lengthMap_self
#print axioms DGCellAttachment.Family.lengthMap_comp
#print axioms DGCellAttachment.Family.exactLengthSet
#print axioms DGCellAttachment.Family.exactLengthHom
#print axioms DGCellAttachment.Family.exactLengthProjection
#print axioms DGCellAttachment.Family.replaceSummand_exactLength_projection
#print axioms DGCellAttachment.Family.replaceRow_exactLength_projection
#print axioms DGCellAttachment.Family.lengthInternalQuotient
#print axioms DGCellAttachment.Family.lengthReplacement_quotient_zero
#print axioms DGCellAttachment.Family.lengthQuotient
#print axioms DGCellAttachment.Family.lengthQuotient_f
#print axioms DGCellAttachment.Family.exactLengthHom_kFlat
#print axioms DGCellAttachment.Family.lengthSet_subset_succ
#print axioms DGCellAttachment.Family.exactLengthSet_subset
#print axioms DGCellAttachment.Family.lengthSet_disjoint_exact_succ
#print axioms DGCellAttachment.Family.lengthSet_partition_succ
#print axioms DGCellAttachment.Family.lengthMap_quotient
#print axioms DGCellAttachment.Family.lengthShortComplex
#print axioms DGCellAttachment.Family.lengthSplitting
#print axioms DGCellAttachment.Family.lengthQuotient_zero_isIso
#print axioms DGCellAttachment.Family.lengthHom_kFlat
#print axioms DGCellAttachment.Family.mem_lengthSet_self
#print axioms DGCellAttachment.Family.lengthDiagram
#print axioms DGCellAttachment.Family.lengthCocone
#print axioms DGCellAttachment.Family.lengthMap_ι
#print axioms DGCellAttachment.Family.lengthEvalIsColimit
#print axioms DGCellAttachment.Family.lengthIsColimit
#print axioms DGCellAttachment.Family.attachedHom_kFlat
#print axioms DGCellAttachment.Family.attachedDGCategory_localHomKFlat
end SerrePositivity.DifferentialGraded
