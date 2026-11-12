module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedSourceSliceInput
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.CompactExtendedPullbackInput
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinQuasicategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallJoin

/-!
概要：指定した片方の compact 始点を含む二成分の小さい追加入力族を構成する。
方針：指定成分は元の under 図式の join 展開、他成分は元の入力のまま使う。
規約：元の成分型と元の全増大余錐を保つ。
使われ方：compact 成分射影の両側の under 試験。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：第一成分だけに指定始点形状を追加した二成分形状。
方針：同じ小さい join と元の入力形状を二点族にする。
規約：全形状は小さい宇宙に保つ。
使われ方：第一成分射影の under 試験。 -/
def firstUnderInputShapes (A K : SSet.{u}) : Fin 2 → SSet.{u} := ![_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K, K]

/-- 概要：第二成分だけに指定始点形状を追加した二成分形状。
方針：元の入力形状と同じ小さい join を二点族にする。
規約：第一脚の同値持ち上げはそのまま保つ。
使われ方：第二成分射影の under 試験。 -/
def secondUnderInputShapes (A K : SSet.{u}) : Fin 2 → SSet.{u} := ![K, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K]

/-- 概要：第一追加入力族の元の入力形状からの包含。
方針：第一成分は join の右包含、第二成分は恒等射。
規約：元の可変入力を厳密に保つ。
使われ方：共通入力への相対制限。 -/
def firstUnderInputInclusions (A K : SSet.{u}) : ∀ c,
    (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (firstUnderInputShapes A K c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)) (𝟙 _)

/-- 概要：第二追加入力族の元の入力形状からの包含。
方針：第一成分は恒等射、第二成分は join の右包含。
規約：第一脚の入力包含は恒等射のまま。
使われ方：第二成分の指定始点を保つ厳密化。 -/
def secondUnderInputInclusions (A K : SSet.{u}) : ∀ c,
    (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (secondUnderInputShapes A K c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K))

variable {A K : SSet.{u}} {B : SSet.{u + 1}} [Quasicategory B]
  {C : Fin 2 → SSet.{u + 1}} [∀ c, Quasicategory (C c)]
  (μ : Cardinal.{u}) (p : ∀ c, C c ⟶ B)
  (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback (p 0) (p 1))
  (U : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)

/-- 概要：第一成分の指定始点を保つ元の対象圏内の全入力族。
方針：第一成分は compact 始域 slice の全展開、第二成分は元の入力射影。
規約：元の二成分型を取り替えない。
使われ方：第一成分 cofinal 試験の実際の交互構成。 -/
def firstUnderInputDiagrams
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.fst (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z) : ∀ c,
    (SSet.uliftFunctor.{u + 1, u}).obj (firstUnderInputShapes A K c) ⟶ C c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInput μ (x ≫ pullback.fst (p 0) (p 1)) t)
    ((U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) ≫ pullback.snd (p 0) (p 1))

/-- 概要：第二成分の指定始点を保つ元の対象圏内の全入力族。
方針：第一成分は元の入力射影、第二成分は compact 始域 slice の全展開。
規約：元の第一脚の同値持ち上げを保つ。
使われ方：第二成分 cofinal 試験の実際の交互構成。 -/
def secondUnderInputDiagrams
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.snd (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z) : ∀ c,
    (SSet.uliftFunctor.{u + 1, u}).obj (secondUnderInputShapes A K c) ⟶ C c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ ((U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) ≫ pullback.fst (p 0) (p 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInput μ (x ≫ pullback.snd (p 0) (p 1)) t)

/-- 概要：第一指定始点を含む全入力族の元の標的への増大余錐。
方針：第一成分は展開余錐、第二成分は元の全余錐の射影。
規約：元の全単体値を保つ。
使われ方：交互構成の固定標的。 -/
def firstUnderInputCocones
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.fst (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z) :
    ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (firstUnderInputDiagrams μ p x U t c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInputCocone μ (x ≫ pullback.fst (p 0) (p 1)) t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.snd (p 0) (p 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone U))

/-- 概要：第二指定始点を含む全入力族の元の標的への増大余錐。
方針：第一成分は元の全余錐の射影、第二成分は展開余錐。
規約：元の第一脚と共通の標的を保持する。
使われ方：第二成分 cofinal 試験の固定標的。 -/
def secondUnderInputCocones
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.snd (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z) :
    ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (secondUnderInputDiagrams μ p x U t c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst (p 0) (p 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone U))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInputCocone μ (x ≫ pullback.snd (p 0) (p 1)) t)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
