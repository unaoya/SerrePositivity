module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningInvertibleTransformation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ResolutionComparisonEdge

/-!
概要：coherent な図式の関手同型による小さい unstraightening の同値不変性。
方針：大きい全空間の底上の比較射を縮小し、fiber ごとの同値判定で元の宇宙へ戻す。
規約：底の quasicategory は宇宙 u、図式の値は 𝒮 の coherent nerve。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、図式を自然な解像で置き換えるときの fibration 側の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：quasicategory 上の小さい unstraightening の全空間は quasicategory。
方針：小さい射影の left fibration 性を inner fibration 性として使う。
規約：図式の strict 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい全空間の比較を quasicategory の同値にする。 -/
instance smallLeftUnstraightening_quasicategory {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)

/-- 概要：coherent な図式の関手同型は小さい unstraightening 間の底上の前合成同値を与える。
方針：大きい比較射の存在を用い、その射と同値性を小さい全空間へ移す。
規約：底は厳密に固定し、全空間の同値だけで終わらせない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい代表における図式の同型に対する不変性。 -/
lemma exists_smallLeftUnstraighteningComparison_of_functorIso
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    ∃ f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G,
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := by
  obtain ⟨f, hf, ef⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftUnstraighteningComparison_of_functorIso η
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningOverMap F G f,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningOverMap_projection F G f hf,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningOverMap_isPrecompositionEquivalence F G f hf ef⟩

/-- 概要：関手同型に対応する小さい unstraightening の底上の比較射を選ぶ。
方針：底を保つ前合成同値の存在定理から順方向の射を取り出す。
規約：選択した射の底の条件と同値性を別の補題で保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較図式で使う具体的な小さい全空間の射。 -/
noncomputable def smallLeftUnstraighteningComparisonOfFunctorIso
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G :=
  (exists_smallLeftUnstraighteningComparison_of_functorIso η).choose

/-- 概要：選択した小さい比較射は元の底を保つ。
方針：選択した存在の証明の第一条件を取り出す。
規約：関手同型 η の選択を固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい相対関手空間への比較射の入力。 -/
lemma smallLeftUnstraighteningComparisonOfFunctorIso_projection
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    smallLeftUnstraighteningComparisonOfFunctorIso η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F :=
  (exists_smallLeftUnstraighteningComparison_of_functorIso η).choose_spec.1

/-- 概要：選択した小さい比較射は全ての quasicategory への前合成同値。
方針：選択した存在の証明の第二条件を取り出す。
規約：順方向は構成済みの小さい比較射そのもの。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の同値不変性への適用。 -/
lemma smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (smallLeftUnstraighteningComparisonOfFunctorIso η) :=
  (exists_smallLeftUnstraighteningComparison_of_functorIso η).choose_spec.2

/-- 概要：関手同型の小さい unstraightening は同じ宇宙の quasicategory として同値。
方針：底上の小さい比較射の前合成同値性から逆射と単位・余単位を得る。
規約：順方向は選択済みの底上の射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な図式の同型を小さい全空間の同値へ移す。 -/
noncomputable def smallLeftUnstraighteningEquivalenceOfFunctorIso
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G) :=
  (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence η).isQCatEquivalence.choose

/-- 概要：図式とその自然な解像の小さい unstraightening は同値。
方針：大域的な解像の関手同型に、小さい unstraightening の同値不変性を適用する。
規約：一般の coherent な図式 F を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類の比較を解像した図式上で行うための置き換え。 -/
noncomputable def smallLeftUnstraighteningResolutionEquivalence
    {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionInfinityMap)) :=
  smallLeftUnstraighteningEquivalenceOfFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionDiagramComparisonIso F)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
