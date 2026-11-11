module
public import SerrePositivity.KST.SConstruction.PerfectStableHoArrow
public import SerrePositivity.KST.SConstruction.PerfectSemiorthogonalDecomposition
public import SerrePositivity.KST.Spectra.CoherentNerve

/-! # Cat^perf の元の射の類の不変量値と半直交分解の切断
概要：同じ完全関手の不変量値の類を取り、元の右包含が射影の切断になると示す。
方針：Cat^perf の h 圏で証明した関手法則と関手同型不変性を、同じ ∞ 関手で写す。
規約：Sp 値を群の値で代用しない。使われ方：実 fiber 列の分裂への入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial
variable (E : perfectStableInfinity.{u} ⟶ Sp.{u})

/-- 同じ不変量値の頂点を、元の h Sp の対象として保持する。 -/
def perfectInvariantHoObject (a : perfectStableInfinity.{u} _⦋0⦌) : hoFunctor.obj Sp.{u} :=
  HomotopyCategory.mk (E.app (Opposite.op ⦋0⦌) a)

/-- 元の同じ完全関手の Cat^perf 辺を写した、h Sp の実際の射。 -/
def perfectInvariantHoArrow {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    perfectInvariantHoObject E (perfectStableVertex A hA) ⟶
      perfectInvariantHoObject E (perfectStableVertex B hB) :=
  (hoFunctor.map E).toFunctor.map (perfectStableHoArrow F hA hB)

/-- 不変量値の射は、同じ元の Cat^perf 辺の像の類そのもの。 -/
lemma perfectInvariantHoArrow_edge {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    perfectInvariantHoArrow E F hA hB =
      Truncated.HomotopyCategory.homMk ((perfectStableArrow F hA hB).map E).toTruncated := rfl

/-- 関手同型を持つ同じ完全関手は、不変量値の同じ射の類を与える。 -/
lemma perfectInvariantHoArrow_eq_of_functorIso {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {F G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    perfectInvariantHoArrow E F hA hB = perfectInvariantHoArrow E G hA hB :=
  congrArg (hoFunctor.map E).toFunctor.map (perfectStableHoArrow_eq_of_functorIso hA hB e)

/-- 元の恒等完全関手の値の類は、同じ対象値の恒等射。 -/
lemma perfectInvariantHoArrow_id (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) :
    perfectInvariantHoArrow E (show A ⟶ A from 𝟙 A) hA hA =
      𝟙 (perfectInvariantHoObject E (perfectStableVertex A hA)) :=
  (congrArg (hoFunctor.map E).toFunctor.map (perfectStableHoArrow_id A hA)).trans
    ((hoFunctor.map E).toFunctor.map_id _)

/-- 同じ元の完全関手の合成は、不変量値の射の類の合成を保持する。 -/
lemma perfectInvariantHoArrow_comp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) :
    perfectInvariantHoArrow E (show A ⟶ C from (F : A ⟶ B) ≫ (G : B ⟶ C)) hA hC =
      perfectInvariantHoArrow E F hA hB ≫ perfectInvariantHoArrow E G hB hC :=
  (congrArg (hoFunctor.map E).toFunctor.map (perfectStableHoArrow_comp F G hA hB hC)).trans
    ((hoFunctor.map E).toFunctor.map_comp _ _)

/-- 半直交分解の元の右包含の値は、同じ射影の値の切断。 -/
lemma perfectSemiorthogonal_value_section {A B T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition A B T)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete T.obj) :
    perfectInvariantHoArrow E d.rightInclusion hB hT ≫
        perfectInvariantHoArrow E d.projection hT hB =
      𝟙 (perfectInvariantHoObject E (perfectStableVertex B hB)) := by
  let c : B ⟶ B := (d.rightInclusion : B ⟶ T) ≫ (d.projection : T ⟶ B)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.hom (𝟙 B : B ⟶ B).hom := d.sectionIso
  exact (perfectInvariantHoArrow_comp E d.rightInclusion d.projection hB hT hB).symm.trans
    ((perfectInvariantHoArrow_eq_of_functorIso E hB hB he).trans
      (perfectInvariantHoArrow_id E B hB))

end SerrePositivity.KST.SConstruction
