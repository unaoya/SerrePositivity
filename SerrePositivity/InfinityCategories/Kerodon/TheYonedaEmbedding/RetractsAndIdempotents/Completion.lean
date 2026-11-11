module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.RetractClosure
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Coherent
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemComplete
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PresheafClosure
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractReflection
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の Yoneda 因子化が冪等完備化を与えることを証明する。
方針：証明済みの冪等完備性・充満忠実性と、元の内部での retract 条件を合わせる。
規約：HTT 5.1.4.1 の定義による存在であり、5.1.4.9 の普遍性は別途証明する。
使われ方：HTT 5.1.4.2 の前層内の冪等完備化。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 冪等完備な標的への充満忠実な関手で、全対象がその像の retract となる条件。 -/
@[kerodon 040U]
def IsIdempotentCompletion {C D : SSet.{u}} (f : C ⟶ D) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete D ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f ∧
    ∀ d : D _⦋0⦌, ∃ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf d (f.app (Opposite.op ⦋0⦌) c)

/-- 元の Idem(C) の各頂点は、同じ Idem(C) 自身の内部で元の Yoneda 像の retract。 -/
lemma idemVertex_retract_idemYoneda {C : SSet.{u}} [Quasicategory C]
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem C) _⦋0⦌) : ∃ x : C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf F ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C).app (Opposite.op ⦋0⦌) (ULift.up x)) := by
  obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemVertex_retract_yoneda F
  refine ⟨x, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isVertexRetractOf_iff_map_of_fullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusionPresheaf C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusionPresheaf_isFullyFaithful C) _ _).mpr ?_⟩
  have he := congrArg
    (fun f : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C ↦
      f.app (Opposite.op ⦋0⦌) (ULift.up x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_inclusion C)
  exact he.symm ▸ hx

/-- 元の全 Yoneda の因子化は、元の前層内の retract 閉包を冪等完備化として与える。 -/
@[kerodon 040Z]
lemma idemYoneda_isIdempotentCompletion (C : SSet.{u}) [Quasicategory C] :
    IsIdempotentCompletion (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idem_isIdempotentComplete C, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isFullyFaithful C, ?_⟩
  intro F
  obtain ⟨x, hx⟩ := idemVertex_retract_idemYoneda F
  exact ⟨ULift.up x, hx⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
