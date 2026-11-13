module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceTrivialFibration
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence

/-!
概要：元のパラメータの二関手を保つ共通の quasicategory 延長と、制限の Hom 全単射。
方針：inner anodyne な制限の充満忠実性と、元の単位の式の自然性を使う。
規約：native な錐の極限性への接続は別工程。使われ方：一般 coherent 極限の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- inner anodyne な制限は、元の指定した両関手間の h Fun の Hom の全単射を与える。 -/
lemma functorHomPrecomp_bijective_of_innerAnodyne {A B X : SSet.{u}} [Quasicategory X]
    (k : A ⟶ B) (hk : innerAnodyneExtensions k) (U V : B ⟶ X) :
    Function.Bijective ((hoFunctor.map ((pre k).app X)).toFunctor.map :
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (k ≫ U) (k ≫ V)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne k hk X
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration ((pre k).app X)).homotopyCategoryMap_bijective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)

/-- 元の二つの関手を、共通の quasicategory パラメータへ厳密に延長する。 -/
lemma exists_quasicategory_common_parameter {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : A ⟶ X) (V : A ⟶ Y) :
    ∃ (B : SSet.{u}) (k : A ⟶ B) (U' : B ⟶ X) (V' : B ⟶ Y),
      innerAnodyneExtensions k ∧ Quasicategory B ∧ k ≫ U' = U ∧ k ≫ V' = V := by
  obtain ⟨B, k, U', hk, hB, _, hU⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_quasicategory_resolution_over U
  have := hk (Limits.terminal.from Y) (InnerFibration.mem (q := Limits.terminal.from Y))
  have sq : CommSq V k (Limits.terminal.from Y) (Limits.terminal.from B) :=
    ⟨Limits.terminal.hom_ext _ _⟩
  exact ⟨B, k, U', sq.lift, hk, hB, hU, sq.fac_left⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
