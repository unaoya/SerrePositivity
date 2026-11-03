module

public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.Retracts
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Core.Idempotent.Coherent
public import SerrePositivity.InfinityCategories.F1.Idempotent.IdemComplete
public import SerrePositivity.InfinityCategories.F1.Idempotent.PresheafClosure
public import SerrePositivity.InfinityCategories.Core.Idempotent.RetractReflection

/-!
概要：元の Yoneda 因子化が冪等完備化を与えることを証明する。
方針：証明済みの冪等完備性・充満忠実性と、元の内部での retract 条件を合わせる。
規約：HTT 5.1.4.1 の定義による存在であり、5.1.4.9 の普遍性は別途証明する。
使われ方：HTT 5.1.4.2 の前層内の冪等完備化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 冪等完備な標的への充満忠実な関手で、全対象がその像の retract となる条件。 -/
def IsIdempotentCompletion {C D : SSet.{u}} (f : C ⟶ D) : Prop :=
  IsIdempotentComplete D ∧ IsFullyFaithful f ∧
    ∀ d : D _⦋0⦌, ∃ c : C _⦋0⦌, IsVertexRetractOf d (f.app (Opposite.op ⦋0⦌) c)

/-- 元の Idem(C) の各頂点は、同じ Idem(C) 自身の内部で元の Yoneda 像の retract。 -/
lemma idemVertex_retract_idemYoneda {C : SSet.{u}} [Quasicategory C]
    (F : (Idem C) _⦋0⦌) : ∃ x : C _⦋0⦌,
      IsVertexRetractOf F ((idemYoneda C).app (Opposite.op ⦋0⦌) (ULift.up x)) := by
  obtain ⟨x, hx⟩ := idemVertex_retract_yoneda F
  refine ⟨x, (isVertexRetractOf_iff_map_of_fullyFaithful (idemInclusionPresheaf C)
    (idemInclusionPresheaf_isFullyFaithful C) _ _).mpr ?_⟩
  have he := congrArg
    (fun f : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity C ↦
      f.app (Opposite.op ⦋0⦌) (ULift.up x)) (idemYoneda_inclusion C)
  exact he.symm ▸ hx

/-- 元の全 Yoneda の因子化は、元の前層内の retract 閉包を冪等完備化として与える。 -/
lemma idemYoneda_isIdempotentCompletion (C : SSet.{u}) [Quasicategory C] :
    IsIdempotentCompletion (idemYoneda C) := by
  refine ⟨idem_isIdempotentComplete C, idemYoneda_isFullyFaithful C, ?_⟩
  intro F
  obtain ⟨x, hx⟩ := idemVertex_retract_idemYoneda F
  exact ⟨ULift.up x, hx⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
