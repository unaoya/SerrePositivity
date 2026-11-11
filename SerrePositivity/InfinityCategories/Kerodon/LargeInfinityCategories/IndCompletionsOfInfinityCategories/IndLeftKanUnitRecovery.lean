module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FullyFaithfulKanUnit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanExtension

/-!
概要：元の Yoneda に沿う左 Kan 拡張の指定単位は可逆で、元の図式を関手同型で回収する。
方針：構成済みの元の Yoneda の充満忠実性を、inner 性を要しない単位定理へ渡す。
規約：指定単位そのものを使う。延長の κ-filtered 保存性はまだ主張しない。
使われ方：Indκ の関手延長の普遍性の本質的全射性への回収比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の Yoneda に沿う左 Kan 拡張の指定単位そのものが関手圏で可逆。 -/
lemma indLeftKanExtension_unit_isIso
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) F₀ G β) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftKanExtension_unit_isIso_of_fullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isFullyFaithful κ C) β hβ

/-- 同じ指定単位の逆による、元の Yoneda 上の同じ図式の回収比較。 -/
def indLeftKanExtensionRecoveryIso
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) F₀ G β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ G) F₀ := by
  have := indLeftKanExtension_unit_isIso κ β hβ
  exact (asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))).symm

/-- 小さい κ-filtered 余極限を持つ標的への左 Kan 延長を、同じ指定単位の可逆性付きで得る。 -/
lemma ind_exists_leftKanExtension_with_recovery [Fact κ.IsRegular]
    (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    ∃ (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C ⟶ D) (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ G)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) F₀ G β ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ G) F₀) := by
  obtain ⟨G, β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension κ hD F₀
  exact ⟨G, β, hβ, ⟨indLeftKanExtensionRecoveryIso κ β hβ⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
