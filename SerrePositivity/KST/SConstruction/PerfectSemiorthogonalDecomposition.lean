module
public import SerrePositivity.KST.SConstruction.PerfectVerdierSequence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition

/-! # Cat^perf の半直交分解と元の Verdier 列
概要：同じ冪等完備安定対象間の実随伴を持つ半直交分解を、Cat^perf の列へ送る。
方針：元の射影の Verdier 普遍性を使用し、既に完備な右因子への恒等完備化を付ける。
規約：元の包含・射影・全写像空間を保持する。使われ方：Tamme の分裂定理。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial

/-- 同じ Cat^perf の実対象の間の、完全射・実随伴・核条件を持つ半直交分解。 -/
abbrev PerfectSemiorthogonalDecomposition
    (a b t : perfectStableInfinity.{u} _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition (perfectStableObject a) (perfectStableObject b)
    (perfectStableObject t)

/-- 元の完全な半直交分解は、同じ商と恒等完備化による Cat^perf の列を与える。 -/
def perfectSemiorthogonalVerdierSequence
    {a b t : perfectStableInfinity.{u} _⦋0⦌} (d : PerfectSemiorthogonalDecomposition a b t) :
    PerfectVerdierSequence.{u} where
  verdier := d.verdierSequence
  left_complete := perfectStableObject_isIdempotentComplete a
  middle_complete := perfectStableObject_isIdempotentComplete t
  right := perfectStableObject b
  completion := ⟨𝟙 (perfectStableObject b).obj,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_id (perfectStableObject b).obj⟩
  isCompletion := ⟨perfectStableObject_isIdempotentComplete b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_id _, by
    intro x
    exact ⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.refl x⟩⟩

/-- 半直交分解の同じ元の右射は、Cat^perf の列の射影として厳密に回収される。 -/
lemma perfectSemiorthogonalVerdierSequence_projection
    {a b t : perfectStableInfinity.{u} _⦋0⦌} (d : PerfectSemiorthogonalDecomposition a b t) :
    (perfectSemiorthogonalVerdierSequence d).projection.hom = d.projection.hom :=
  Category.comp_id _

end SerrePositivity.KST.SConstruction
