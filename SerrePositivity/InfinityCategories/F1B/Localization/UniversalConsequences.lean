module

public import SerrePositivity.InfinityCategories.F1B.Localization.PrecompositionCriterion

/-!
概要：元の任意の局所化から、全前合成の充満忠実性と実関手同型付き延長を取り出す。
方針：反転関手圏の同値を全包含と合成し、各元の反転関手を元の頂点で表示する。
規約：元と同じ宇宙の標的。反射や随伴を仮定しない。
使われ方：局所化の宇宙持ち上げ・降下で普遍性の二つの成分を照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 局所化に沿う前合成は、周囲の関手圏への射としても充満忠実。 -/
lemma IsLocalization.precomposition_isFullyFaithful {X D : SSet.{u}} {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (h : IsLocalization F W) (K : SSet.{u}) [Quasicategory K] :
    IsFullyFaithful ((pre F).app K) := by
  rw [← localizationPrecomposition_ι F W h.choose K]
  exact (h.choose_spec K).isFullyFaithful.comp
    (isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

/-- 概要：元の反転関手は同じ局所化に沿って実関手と全自然同型付きで延長できる。
方針：元の反転頂点への本質的全射性。
規約：同じ全関手 L。使われ方：普遍性の延長部分と宇宙移送。 -/
lemma IsLocalization.exists_extension {X D E : SSet.{u}} [Quasicategory E] {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (hF : IsLocalization F W) (L : X ⟶ E) (hL : InvertsEdges L W) :
    ∃ G : D ⟶ E, Nonempty (FunctorIso (F ≫ G) L) := by
  obtain ⟨hW, hF⟩ := hF
  let b : (invertingFunctors X E W : SSet.{u}) _⦋0⦌ := ⟨functorVertex L, by
    intro v
    have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst v
    rw [op_id, Functor.map_id_apply]
    change InvertsEdges ((functorVertexEquiv X E).symm ((functorVertexEquiv X E) L)) W
    simpa only [Equiv.symm_apply_apply] using hL⟩
  obtain ⟨a, ⟨e⟩⟩ := (hF E).choose.isEssentiallySurjective b
  obtain ⟨G, rfl⟩ := (functorVertexEquiv D E).surjective a
  have ha : (invertingFunctors X E W).ι.app (Opposite.op ⦋0⦌)
      ((localizationPrecomposition F W hW E).app (Opposite.op ⦋0⦌) (functorVertex G)) =
      functorVertex (F ≫ G) :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (functorVertex G))
      (localizationPrecomposition_ι F W hW E)
  exact ⟨G, ⟨(eqToIso (congrArg HomotopyCategory.mk ha)).symm ≪≫
    VertexIso.map e (invertingFunctors X E W).ι⟩⟩

end SerrePositivity.InfinityCategories
