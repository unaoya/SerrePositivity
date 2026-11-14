module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PrecompositionCriterion

/-!
概要：元の任意の局所化から、全前合成の充満忠実性と実関手同型付き延長を取り出す。
方針：反転関手圏の同値を全包含と合成し、各元の反転関手を元の頂点で表示する。
規約：元と同じ宇宙の標的。反射や随伴を仮定しない。
使われ方：局所化の宇宙持ち上げ・降下で普遍性の二つの成分を照合する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences
/-- 局所化に沿う前合成は、周囲の関手圏への射としても充満忠実。 -/
lemma IsLocalization.precomposition_isFullyFaithful {X D : SSet.{u}} {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) (K : SSet.{u}) [Quasicategory K] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre F).app K) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι F W h.choose K]
  exact (h.choose_spec K).isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization (precomposition_isFullyFaithful)


/-- 概要：元の反転関手は同じ局所化に沿って実関手と全自然同型付きで延長できる。
方針：元の反転頂点への本質的全射性。
規約：同じ全関手 L。使われ方：普遍性の延長部分と宇宙移送。 -/
lemma IsLocalization.exists_extension {X D E : SSet.{u}} [Quasicategory E] {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) (L : X ⟶ E) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges L W) :
    ∃ G : D ⟶ E, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ G) L) := by
  obtain ⟨hW, hF⟩ := hF
  let b : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L, by
    intro v
    have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst v
    rw [op_id, Functor.map_id_apply]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E) L)) W
    simpa only [Equiv.symm_apply_apply] using hL⟩
  obtain ⟨a, ⟨e⟩⟩ := (hF E).choose.isEssentiallySurjective b
  obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv D E).surjective a
  have ha : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W).ι.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition F W hW E).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ G) :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι F W hW E)
  exact ⟨G, ⟨(eqToIso (congrArg HomotopyCategory.mk ha)).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W).ι⟩⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization (exists_extension)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.4.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful
attribute [cite HTT "5.2.7.12" (partial := special) "仮定：局所化が充満部分圏への反射 r として与えられ、任意の標的準圏 D を取る（Lean が強い：包含を右随伴として指定した形）。結論：元の全関手準圏で前合成が充満忠実で、本質像は反射が反転する全辺を反転する関手（この場合に一致）。明示的な逆と両往復の FunctorIso があり、core や関手の同値類の集合だけの普遍性ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful
attribute [cite HTT "5.2.7.3" (partial := special) "仮定：充満包含への反射 r と任意の準圏 E（Lean が強い：右随伴が充満包含の形）。結論：r.reflector に沿う前合成は全関手圏で充満忠実で、その本質像は r.reflector が反転する全辺を反転する関手（この場合に一致）。明示的な QCatEquivalence が反転関手の全部分圏へ与えられる。一般の辺集合の局所化に右随伴があるという逆の主張は型に含めない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful
