module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectIdempotentCompleteGeneral

/-!
概要：固定した厳密 dg 入力の ν 値の coherent 冪等完備性。
方針：D の実 Perf の完備性を、同じ評価同値で元の ν 値へ戻す。
規約：H⁰ からの比較は D 正本を使う。使われ方：実 dg 入力の Cat^perf 接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R]

/-- 概要：任意の厳密 dg 入力の元の ν 値は冪等完備。
方針：実 Perf nerve の完備性を同じ評価同値の逆で運ぶ。
規約：ν の模型を置換しない。使われ方：LT の四対象の完備性を除去する。 -/
lemma dgKInputStableValue_isIdempotentComplete (P : PerfDGInput.{u, v} R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (dgKInputStableValue R P).obj :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R P).of_equivalence
    (presentedPerfectDGQCatEvaluationEquivalence R P).symm

end SerrePositivity.KST.SConstruction
