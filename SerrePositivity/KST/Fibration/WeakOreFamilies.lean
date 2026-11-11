module
public import SerrePositivity.KST.Fibration.WeakOreSquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement

/-! # 元の W 辺の普遍 Ore 補完の全境界に対する相対延長と選択空間 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)

/-- 元の W cospan と指定済みの任意の部分族を固定し、普遍 Ore 四角形を全体へ延長する。 -/
theorem exists_relative_weakOreFamily {S T : SSet.{u}} (j : S ⟶ T) [Mono j]
    (d : T ⟶ weakDenominatorCospans i) (a : S ⟶ weakOreDiagrams i)
    (ha : a ≫ weakOreProjection i = j ≫ d) :
    ∃ F : T ⟶ weakOreDiagrams i, j ≫ F = a ∧ F ≫ weakOreProjection i = d := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := weakOreProjection i) j inferInstance
  have sq : CommSq a j (weakOreProjection i) d := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 同じ全 cospan 族に対する普遍 Ore 補完の全選択空間。 -/
def weakOreFamilySpace {T : SSet.{u}} (d : T ⟶ weakDenominatorCospans i) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom T).map (weakOreProjection i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

/-- 全パラメータ上の選択空間は contractible Kan であり、頂点ごとの存在だけではない。 -/
theorem weakOreFamilySpace_isContractibleKan {T : SSet.{u}}
    (d : T ⟶ weakDenominatorCospans i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (weakOreFamilySpace i d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan ((ihom T).map (weakOreProjection i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

/-- 同じ実 cospan 族を持つ二つの全 Ore 族は、全関手圏内で自然同型。 -/
def weakOreFamiliesIso {T : SSet.{u}} (d : T ⟶ weakDenominatorCospans i)
    (F G : T ⟶ weakOreDiagrams i)
    (hF : F ≫ weakOreProjection i = d) (hG : G ≫ weakOreProjection i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (weakOreProjection i) F G (hF.trans hG.symm)

end SerrePositivity.KST.Fibration
