module

public import SerrePositivity.InfinityCategories.F1B.Localization
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
# 全反転関手圏の前合成同値から元の関手を延長する

概要：指定の反転関手を、同じ局所化写像に沿う全関手同型付き延長へ戻す。
方針：全反転関手 ∞ 圏の本質的全射性と元の全部分複体の包含を使う。
規約：元の全関手と全比較を保持し、頂点ごとの延長で代用しない。
使われ方：既存 CAlg_R の普遍性による D(R) 値忘却の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed Opposite SSet
open scoped Simplicial

lemma localization_extension_exists {X Q E : SSet.{u}}
    [Quasicategory Q] [Quasicategory E]
    (q : X ⟶ Q) (W : Set (X _⦋1⦌)) (hq : InvertsEdges q W)
    (h : IsQCatEquivalence (localizationPrecomposition q W hq E))
    (F : X ⟶ E) (hF : InvertsEdges F W) :
    ∃ G : Q ⟶ E, Nonempty (FunctorIso (q ≫ G) F) := by
  let b : (invertingFunctors X E W : SSet.{u}) _⦋0⦌ := ⟨functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, Functor.map_id_apply]
    change InvertsEdges ((functorVertexEquiv X E).symm ((functorVertexEquiv X E) F)) W
    rw [Equiv.symm_apply_apply]
    exact hF⟩
  obtain ⟨a, ⟨e⟩⟩ := h.choose.isEssentiallySurjective b
  let G := (functorVertexEquiv Q E).symm a
  have ha : functorVertex G = a := (functorVertexEquiv Q E).apply_symm_apply a
  have hi := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (functorVertex G))
    (localizationPrecomposition_ι q W hq E)
  change (invertingFunctors X E W).ι.app (Opposite.op ⦋0⦌)
    ((localizationPrecomposition q W hq E).app (Opposite.op ⦋0⦌) (functorVertex G)) =
      functorVertex (q ≫ G) at hi
  rw [ha] at hi
  refine ⟨G, ⟨?_⟩⟩
  exact (eqToIso (congrArg HomotopyCategory.mk hi)).symm ≪≫
    VertexIso.map e (invertingFunctors X E W).ι

end SerrePositivity.EInfinity.FrameHom
