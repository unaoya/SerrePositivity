module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.PerfectStableInfinity
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion

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

open scoped Simplicial

/-- Cat^perf の列を、実商とその元の冪等完備化で提示するデータ。 -/
structure PerfectVerdierSequence where
  verdier : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}
  left_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete verdier.left.obj
  middle_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete verdier.middle.obj
  right : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}
  completion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap verdier.right right
  isCompletion : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion completion.hom

namespace PerfectVerdierSequence
variable (d : PerfectVerdierSequence.{u})

/-- 列の右端は、実商の元の冪等完備化である。 -/
lemma right_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete d.right.obj := d.isCompletion.1

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
def projection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.verdier.middle d.right :=
  ⟨d.verdier.projection.hom ≫ d.completion.hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _⟩

/-- 元の包含は全写像空間について充満忠実。 -/
lemma inclusion_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful d.verdier.inclusion.hom :=
  d.verdier.isVerdier.fullyFaithful

/-- 冪等完備化後の同じ右射も、元の包含の全対象を零に送る。 -/
lemma projection_kills_inclusion (a : d.verdier.left.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((d.verdier.inclusion.hom ≫ d.projection.hom).app (Opposite.op ⦋0⦌) a) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((d.verdier.inclusion.hom ≫ d.verdier.projection.hom ≫
    d.completion.hom).app (Opposite.op ⦋0⦌) a)
  rw [← Category.assoc]
  exact @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ d.completion.hom d.completion.isExact _
    (d.verdier.isVerdier.kills_inclusion a)

end PerfectVerdierSequence
end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Def 1.2" (partial := special) "仮定：実 Verdier 商の完備化を提示し、標的は Sp、filtered 余極限保存も要求する（Lean が強い）。結論：Cat^perf での完全列とその像のファイバー条件。任意の安定標的を扱う Land–Tamme の定義より狭い（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.PerfectVerdierSequence
