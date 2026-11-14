module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SimplicialBarIndex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsCoproductLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ColimitFromLocalLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationUlift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation

/-!
概要：小余積と小さい幾何学的実現から全小余極限を構成する。
方針：任意の全図式を全単体へ展開し、次数ごとの小余積とその実現を合成する。
規約：元の任意の小さい単体集合形状を扱い、追加の局所化存在を仮定しない。
使われ方：P_Σ 専用反映のための余完備性の構成。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 概要：小余積と小さい幾何学的実現を持つ圏では、元の任意の小さい全図式が余極限を持つ。
方針：全単体の次数射影に沿う局所余極限を小余積で構成し、その実現から元の図式へ戻す。
規約：元の形状の quasicategory 性や標的の全小余極限を仮定しない。
使われ方：P_Σ 専用反映と小余極限保存の判定。 -/
lemma hasSmallColimits_of_coproducts_geometricRealizations
    {X : SSet.{u + 1}} [Quasicategory X]
    (hcop : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X) (hgeom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallGeometricRealizations X) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X := by
  intro K F
  let Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialBarSimplexFamily K
  let j := (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap K)
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialBarIndexNerveIso K)
  let F' := e.hom ≫ (j ≫ F)
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_of_localLeftKan_colimits
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) F'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproduct_leftKanDiagram_hasColimit Y hcop F') hgeom
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre j).app X) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localization_pre_isFullyFaithful
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} K) X
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre e.hom).app X) :=
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e) X).isFullyFaithful
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_fullyFaithfulPrecomposition j hj F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_fullyFaithfulPrecomposition e.hom he (j ≫ F) hx)

/-- 概要：全小余極限の存在は、小余積と小さい幾何学的実現の存在と同値。
方針：構成した十分条件と二種類の形状への制限を組み合わせる。
規約：元の標的と同じ宇宙に関する同値である。
使われ方：小余極限存在の公開判定。 -/
lemma hasSmallColimits_iff_coproducts_geometricRealizations
    {X : SSet.{u + 1}} [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallGeometricRealizations X :=
  ⟨fun h ↦ ⟨h.hasSmallCoproducts, h.hasSmallGeometricRealizations⟩,
    fun h ↦ hasSmallColimits_of_coproducts_geometricRealizations h.1 h.2⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.3.10" (partial := stronger-hyp) "仮定：小余積と幾何学的実現（Lean が強い：HA は有限余積で足りる）。結論：小余極限の存在と保存（Lean が強い：有限の場合を含む。Lean が弱い：n 圏での逆向きはこの型にない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasSmallColimits_of_coproducts_geometricRealizations
attribute [cite HA "1.4.4.1" (partial := component) "仮定：小余積と有限余極限の存在・保存、または小余積と幾何学的実現（Lean が強い：HA は安定性から有限余極限を使い小余積だけを条件とする）。結論：小余極限の存在・保存の判定（Lean が弱い：コンパクト性の有限部分余積による判定は型にない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasSmallColimits_iff_coproducts_geometricRealizations
