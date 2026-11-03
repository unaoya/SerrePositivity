module
public import SerrePositivity.KST.SConstruction.PerfectStableInfinity
public import SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence
public import SerrePositivity.InfinityCategories.F1.Idempotent.Completion

/-! # 冪等完備な安定 ∞ 圏の Verdier 列の実提示
概要：実 Verdier 商とその冪等完備化を保持し、Cat^perf の exact 列を提示する。
方針：既存の全関手圏における商の普遍性と、N の実冪等完備化条件を組み合わせる。
規約：商自体の冪等完備性を要求しない。使われ方：BGT (a) の非連結 K の入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open F2.Idempotent
open scoped Simplicial

/-- Cat^perf の列を、実商とその元の冪等完備化で提示するデータ。 -/
structure PerfectVerdierSequence where
  verdier : VerdierSequence.{u}
  left_complete : IsIdempotentComplete verdier.left.obj
  middle_complete : IsIdempotentComplete verdier.middle.obj
  right : StableCategory.{u}
  completion : ExactMap verdier.right right
  isCompletion : IsIdempotentCompletion completion.hom

namespace PerfectVerdierSequence
variable (d : PerfectVerdierSequence.{u})

/-- 列の右端は、実商の元の冪等完備化である。 -/
lemma right_complete : IsIdempotentComplete d.right.obj := d.isCompletion.1

/-- Cat^perf における左端の実頂点。 -/
def leftVertex : perfectStableInfinity.{u} _⦋0⦌ :=
  perfectStableVertex d.verdier.left d.left_complete

/-- Cat^perf における中央の実頂点。 -/
def middleVertex : perfectStableInfinity.{u} _⦋0⦌ :=
  perfectStableVertex d.verdier.middle d.middle_complete

/-- Cat^perf における、商の冪等完備化の実頂点。 -/
def rightVertex : perfectStableInfinity.{u} _⦋0⦌ :=
  perfectStableVertex d.right d.right_complete

/-- 同じ実商射と冪等完備化の合成による、列の元の右射。 -/
def projection : ExactMap d.verdier.middle d.right :=
  ⟨d.verdier.projection.hom ≫ d.completion.hom, isExactFunctor_comp _ _⟩

/-- 元の包含は全写像空間について充満忠実。 -/
lemma inclusion_isFullyFaithful : IsFullyFaithful d.verdier.inclusion.hom :=
  d.verdier.isVerdier.fullyFaithful

/-- 冪等完備化後の同じ右射も、元の包含の全対象を零に送る。 -/
lemma projection_kills_inclusion (a : d.verdier.left.obj _⦋0⦌) :
    IsZeroVertex ((d.verdier.inclusion.hom ≫ d.projection.hom).app (Opposite.op ⦋0⦌) a) := by
  change IsZeroVertex ((d.verdier.inclusion.hom ≫ d.verdier.projection.hom ≫
    d.completion.hom).app (Opposite.op ⦋0⦌) a)
  rw [← Category.assoc]
  exact @IsExactFunctor.preservesZero _ _ d.completion.hom d.completion.isExact _
    (d.verdier.isVerdier.kills_inclusion a)

end PerfectVerdierSequence
end SerrePositivity.KST.SConstruction
