module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PresheafSubcategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.FunctorSpaceVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：元の小さい coherent 図式全体への Ind Yoneda の作用。
方針：全内部 Hom の宇宙同型と元の Yoneda による後合成を使う。
規約：辺・高次単体を保持。使われ方：有限図式の単一 filtered 表示。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の全 coherent 図式と変換を同じ Ind Yoneda で写す全射。 -/
def diagramYoneda (κ : Cardinal.{u}) (K C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj ((ihom K).obj C) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso K C).hom ≫
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)

/-- 指定図式の像は元の全図式の持ち上げと Yoneda の合成そのもの。 -/
lemma diagramYoneda_vertex (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
    (a : K ⟶ C) :
    (diagramYoneda κ K C).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) := by
  change ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso K C).hom.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftFunctorSpaceIso_hom_vertex]
  rfl

/-- 元の全作用は形状の任意の制限と全次数で厳密に可換。 -/
lemma diagramYoneda_restrict (κ : Cardinal.{u}) {J K C : SSet.{u}}
    [Quasicategory C] (f : J ⟶ K) :
    (SSet.uliftFunctor.{u + 1, u}).map ((pre f).app C) ≫ diagramYoneda κ J C =
      diagramYoneda κ K C ≫ ((pre ((SSet.uliftFunctor.{u + 1, u}).map f)).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 元の図式版 Yoneda は全写像空間で充満忠実。形状の有限性も不要。 -/
lemma diagramYoneda_isFullyFaithful (κ : Cardinal.{u}) (K C : SSet.{u})
    [Quasicategory C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (diagramYoneda κ K C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso K C)).isQCatEquivalence.isFullyFaithful.comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isFullyFaithful κ C).postcompose ((SSet.uliftFunctor.{u + 1, u}).obj K))

/-- 図式 Yoneda の全作用は、元の任意の頂点での評価と厳密に可換。 -/
lemma diagramYoneda_evaluate (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
    (k : K _⦋0⦌) :
    diagramYoneda κ K C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) (ULift.up k) =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
