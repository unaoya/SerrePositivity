module
public import SerrePositivity.KST.SConstruction.PerfectStableArrow
public import SerrePositivity.KST.LocalizingInvariants.StableValueFunctor

/-! # Cat^perf の元の完全関手の射の類と関手法則
概要：同じ完全関手の Cat^perf の辺の類は、恒等・合成・関手同型を保持する。
方針：元の包含の h 圏での忠実性により、StableInfinity の同じ射の類で検証する。
規約：完全関手の代表を選び直さない。使われ方：半直交分解の切断の不変量値。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 元の Cat^perf 包含の h 圏での忠実性。 -/
local instance perfectStableInclusionHo_faithful :
    (hoFunctor.map perfectStableInfinityInclusion.{u}).toFunctor.Faithful :=
  perfectStableInfinityInclusion_isFullyFaithful.toHoFullyFaithful.faithful

/-- 同じ元の完全関手が定める Cat^perf の h 圏の射。 -/
def perfectStableHoArrow {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    HomotopyCategory.mk (perfectStableVertex A hA) ⟶
      HomotopyCategory.mk (perfectStableVertex B hB) :=
  Truncated.HomotopyCategory.homMk (perfectStableArrow F hA hB).toTruncated

/-- 同じ射の類を含めると、元の完全関手の StableInfinity の射の類を回収する。 -/
lemma perfectStableHoArrow_inclusion {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    (hoFunctor.map perfectStableInfinityInclusion).toFunctor.map
        (perfectStableHoArrow F hA hB) = stableHoFunctor.map F := by
  change Truncated.HomotopyCategory.homMk
    ((perfectStableArrow F hA hB).map perfectStableInfinityInclusion).toTruncated = _
  have h := congrArg SSet.yonedaEquiv (perfectStableArrow_inclusion F hA hB)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact congrArg Truncated.HomotopyCategory.homMk (Truncated.Edge.ext h)

/-- 元の完全関手の関手同型は、同じ Cat^perf の射の類を等しくする。 -/
lemma perfectStableHoArrow_eq_of_functorIso {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {F G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    perfectStableHoArrow F hA hB = perfectStableHoArrow G hA hB := by
  apply (hoFunctor.map perfectStableInfinityInclusion).toFunctor.map_injective
  rw [perfectStableHoArrow_inclusion, perfectStableHoArrow_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.stableArrow_homMk_eq_of_functorIso e

/-- 同じ元の恒等完全関手の辺の類は、Cat^perf の恒等射。 -/
lemma perfectStableHoArrow_id (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) :
    perfectStableHoArrow (show A ⟶ A from 𝟙 A) hA hA =
      𝟙 (HomotopyCategory.mk (perfectStableVertex A hA)) := by
  apply (hoFunctor.map perfectStableInfinityInclusion).toFunctor.map_injective
  exact (perfectStableHoArrow_inclusion (show A ⟶ A from 𝟙 A) hA hA).trans
    ((stableHoFunctor.map_id A).trans
      ((hoFunctor.map perfectStableInfinityInclusion).toFunctor.map_id
        (HomotopyCategory.mk (perfectStableVertex A hA))).symm)

/-- 同じ完全関手の合成は、元の Cat^perf の射の類の合成を保つ。 -/
lemma perfectStableHoArrow_comp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) :
    perfectStableHoArrow (show A ⟶ C from (F : A ⟶ B) ≫ (G : B ⟶ C)) hA hC =
      perfectStableHoArrow F hA hB ≫ perfectStableHoArrow G hB hC := by
  apply (hoFunctor.map perfectStableInfinityInclusion).toFunctor.map_injective
  rw [Functor.map_comp, perfectStableHoArrow_inclusion,
    perfectStableHoArrow_inclusion, perfectStableHoArrow_inclusion]
  exact stableHoFunctor.map_comp F G

end SerrePositivity.KST.SConstruction
