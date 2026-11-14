module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactFunctorCategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
/-!
概要：零化完全関手圏への前合成の充満忠実性と本質的全射性を判定する。
方針：全関手圏の充満忠実性を全部分圏へ制限し、完全な実延長を持ち上げる。
規約：自然変換の全高次を保持。使われ方：安定 Verdier 商の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 全関手圏で充満忠実な前合成は、零化完全関手の全 ∞ 部分圏でも充満忠実。 -/
lemma zeroingExactPrecomposition_isFullyFaithful {X Q Y : SSet.{u}} [Quasicategory Y]
    (q : X ⟶ Q) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q] (P : Set (X _⦋0⦌))
    (hq : ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.app (Opposite.op ⦋0⦌) x))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre q).app Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition q P hq Y) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom Q).obj Y)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.IsExactFunctorVertex Q Y)
  have ht := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj Y)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.IsZeroingExactFunctorVertex X Y P)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactFunctors X Y P).ι at ht
  apply ht.cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition_ι]
  exact hi.comp hf
/-- 完全な実延長の存在は、全零化完全関手圏への本質的全射性を与える。 -/
lemma zeroingExactPrecomposition_isEssentiallySurjective {X Q Y : SSet.{u}}
    [Quasicategory Y] (q : X ⟶ Q) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q] (P : Set (X _⦋0⦌))
    (hq : ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.app (Opposite.op ⦋0⦌) x))
    (he : ∀ F : X ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F →
      (∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)) →
      ∃ G : Q ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ G) F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition q P hq Y) := by
  intro b
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).symm b.val
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = b.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).apply_symm_apply b.val
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F ∧ ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex b
  obtain ⟨G, hG, ⟨e⟩⟩ := he F hb.1 hb.2
  let a : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactFunctors Q Y : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, by
    intro α
    rw [SimplexCategory.hom_zero_zero α]
    simp only [op_id, Functor.map_id_apply]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.isExactFunctorVertex_functorVertex Q Y G).mpr hG⟩
  let c := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition q P hq Y).app (Opposite.op ⦋0⦌) a
  have hc : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactFunctors X Y P).ι.app (Opposite.op ⦋0⦌) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (q ≫ G) := congrArg (fun f => f.app (Opposite.op ⦋0⦌) a)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition_ι q P hq Y)
  let J : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactFunctors X Y P).ι.app (Opposite.op ⦋0⦌) c)
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactFunctors X Y P).ι.app (Opposite.op ⦋0⦌) b) :=
    eqToIso (congrArg HomotopyCategory.mk hc) ≪≫ e ≪≫
      eqToIso (congrArg HomotopyCategory.mk hv)
  let ff := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj Y)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.IsZeroingExactFunctorVertex X Y P)).toHoFullyFaithful
  exact ⟨a, ⟨ff.preimageIso J⟩⟩
/-- 全関手圏での充満忠実性と完全延長の存在による全零化完全関手 ∞ 圏の同値判定。 -/
lemma zeroingExactPrecomposition_isQCatEquivalence {X Q Y : SSet.{u}} [Quasicategory Y]
    (q : X ⟶ Q) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q] (P : Set (X _⦋0⦌))
    (hq : ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.app (Opposite.op ⦋0⦌) x))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre q).app Y))
    (he : ∀ F : X ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F →
      (∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)) →
      ∃ G : Q ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ G) F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition q P hq Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (zeroingExactPrecomposition_isFullyFaithful q P hq hf)
    (zeroingExactPrecomposition_isEssentiallySurjective q P hq he)
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
