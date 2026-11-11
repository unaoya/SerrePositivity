module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionsFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence

/-!
概要：任意の quasicategory 上の left fibrations の fiber 同値は切断空間の同値を誘導する。
方針：相対関手空間との同型の自然性を使い、F1 の底上の逆射による後合成同値を移す。
規約：全空間の比較射に fibration 性を要求しない。
使われ方：Kerodon 5.6.0.6（Tag 028T）、7.4.1.6（Tag 05QS）、HTT 4.2.4.1 の一般の切断比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-- 概要：切断空間と相対関手空間の同型は底上の後合成と可換。
方針：相対関手の族を展開し、切断の評価の後合成の式で比較する。
規約：底 K と二つの射影の充填性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、切断空間への相対後合成の同値性の移送。 -/
lemma simplicialSectionsRelativeIso_naturality {K E E' : SSet.{u}}
    (p : E ⟶ K) (q : E' ⟶ K) (f : E ⟶ E') (hf : f ≫ q = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsRelativeIso q).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsRelativeIso p).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf (𝟙 K) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective q (𝟙 K)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeSectionsUncurry_comp]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsRelativeIso, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_evaluation f hf

/-- 概要：任意の quasicategory 上の fiber ごとの同値は切断空間のホモトピー同値を与える。
方針：fiber 同値から底上の前合成同値を得て相対後合成へ移し、標準同型を消去する。
規約：底の形状と比較射 f の充填性に追加の条件を要求しない。
使われ方：Kerodon 5.6.0.6（Tag 028T）、7.4.1.6（Tag 05QS）、HTT 4.2.4.1 の coherent な錐の一般比較。 -/
lemma simplicialSectionsMap_homotopyEquivalence_of_fibers
    {K E E' : SSet.{u}} [Quasicategory K]
    (p : E ⟶ K) (q : E' ⟶ K) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex q
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    p q f hf (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isPrecompositionEquivalence_of_leftFibration_fibers p q f hf h) (𝟙 K)
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsRelativeIso p)).isQCatEquivalence
  have hq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsRelativeIso q)).isQCatEquivalence
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence
  apply hq.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsRelativeIso q).hom)
  rw [simplicialSectionsRelativeIso_naturality]
  exact hp.comp he

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
