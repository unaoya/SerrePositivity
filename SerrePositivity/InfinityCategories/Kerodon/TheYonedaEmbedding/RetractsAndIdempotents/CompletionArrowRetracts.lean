module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.ArrowRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.EssentialImageDiagram

/-!
概要：元の任意の冪等完備化の全ての辺は、元の辺の全関手 ∞ 圏内の retract。
方針：両端の元の retract を順に全辺へ持ち上げ、充満忠実性で元の始域の辺を回収。
規約：比較と retract は辺全体の関手 ∞ 圏内。端点や辺の類だけの分解にしない。
使われ方：HA 1.1.3.7 の新しい辺の fiber/cofiber の構成。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の任意の冪等完備化の辺は、元の始域の辺の像の全関手 ∞ 圏内の retract。 -/
lemma IsIdempotentCompletion.arrow_retract {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    (a : (Δ[1] : SSet.{u}) ⟶ D) :
    ∃ b : (Δ[1] : SSet.{u}) ⟶ C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b ≫ f)) := by
  obtain ⟨x, ⟨rx⟩⟩ := hf.2.2 (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a))
  obtain ⟨y, ⟨ry⟩⟩ := hf.2.2 (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ a))
  obtain ⟨b, hbx, hby, hab⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.arrow_retract_lift a
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) rx ry
  have hg : ∀ k : (Δ[1] : SSet.{u}) _⦋0⦌, ∃ c : C _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) c) (b.app (Opposite.op ⦋0⦌) k)) := by
    intro k
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
    fin_cases i
    · refine ⟨x, ?_⟩
      change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) x)
        (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
      have h₀ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
          stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
      rw [SSet.yonedaEquiv_comp, h₀] at hbx
      rw [hbx]
      exact ⟨Iso.refl _⟩
    · refine ⟨y, ?_⟩
      change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) y)
        (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
      have h₁ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
          stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
      rw [SSet.yonedaEquiv_comp, h₁] at hby
      rw [hby]
      exact ⟨Iso.refl _⟩
  obtain ⟨c, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_diagram_in_fullyFaithful_source f hf.2.1 b hg
  exact ⟨c, hab.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e.symm)⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
