module
public import SerrePositivity.KST.SConstruction.PerfectLaxCategory

/-! # Tamme の同じ lax pullback の Cat^perf Verdier 列
概要：元の左包含・右包含・第一射影を持つ分裂列を、元の実商と完備化の提示へ接続する。
方針：同じ lax pullback の半直交分解を、既存の全提示列の構成に渡す。
規約：商の第一射影と元の三頂点を厳密に回収する。使われ方：Tamme の分裂定理。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B)
  (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete D.obj)

/-- 元の第一射影を商とする、同じ lax pullback の実 Cat^perf 列。 -/
def tammePerfectSequence : PerfectVerdierSequence.{u} :=
  perfectSemiorthogonalVerdierSequence (perfectLaxSemiorthogonal p q hC hD)

/-- 同じ分裂列は、元の D・lax pullback・C の三頂点を厳密に回収する。 -/
lemma tammePerfectSequence_vertices :
    (tammePerfectSequence p q hC hD).leftVertex = perfectStableVertex D hD ∧
      (tammePerfectSequence p q hC hD).middleVertex = perfectLaxVertex p q hC hD ∧
      (tammePerfectSequence p q hC hD).rightVertex = perfectStableVertex C hC :=
  ⟨rfl, rfl, rfl⟩

/-- 元の第一射影は、提示列の完備化後の射影として回収される。 -/
lemma tammePerfectSequence_projection :
    (tammePerfectSequence p q hC hD).projection.hom = (laxFst p q).hom :=
  perfectSemiorthogonalVerdierSequence_projection (perfectLaxSemiorthogonal p q hC hD)

end SerrePositivity.KST.SConstruction
