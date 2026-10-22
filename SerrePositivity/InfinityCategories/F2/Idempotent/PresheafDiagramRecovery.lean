module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteYonedaRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.EssentialImageDiagram

/-!
概要：元の各値が Yoneda 像の retract である全前層図式を、冪等完備な元の標的へ戻す。
方針：元の各 retract の表現可能性と本質像への全図式の因子化を使い、宇宙を降ろす。
規約：元の全図式を全自然同型まで回収し、各点の対象の選択だけで代用しない。
使われ方：HTT 5.1.4.8 の前層に値を持つ左 Kan 延長から元の標的への回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 全値が元の Yoneda retract 閉包にある前層図式を、元の冪等完備な標的の全図式へ戻す。 -/
lemma exists_diagram_of_retract_presheaves {K E : SSet.{u}} [Quasicategory E]
    (hE : IsIdempotentComplete E)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ PresheafInfinity E)
    (hG : ∀ k, IsRetractPresheaf (G.app (Opposite.op ⦋0⦌) k)) :
    ∃ F : K ⟶ E, Nonempty (FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ yonedaInfinityMap E) G) := by
  obtain ⟨F, hF⟩ := exists_diagram_in_fullyFaithful_source (yonedaInfinityMap E)
    (yonedaInfinityMap_isFullyFaithful E) G (fun k ↦ by
      obtain ⟨e, ⟨he⟩⟩ :=
        (isRetractPresheaf_iff_representable_of_complete hE _).mp (hG k)
      exact ⟨ULift.up e, ⟨he.symm⟩⟩)
  refine ⟨(SSet.uliftFunctor.{u + 1, u}).preimage F, ?_⟩
  rw [Functor.map_preimage]
  exact hF

end SerrePositivity.InfinityCategories.F2.Idempotent
