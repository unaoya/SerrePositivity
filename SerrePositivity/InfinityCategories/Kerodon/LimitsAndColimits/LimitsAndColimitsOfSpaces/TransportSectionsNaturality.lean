module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.TransportPostcomparison

/-!
概要：切断空間と strict transport の end の標準比較は全空間の射について自然である。
方針：under 圏への制限と後合成が可換なことを評価で示し、錐の比較の自然性を使う。
規約：底を保つ実際の射を使い、全空間の同値性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の fiber ごとの比較を切断空間の比較へ移す可換図式。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {I : Type u} [SmallCategory I] {E E' : SSet.{u}}

/-- 概要：切断の under 圏への制限は底を保つ全空間の後合成と可換である。
方針：相対関手を展開し、直積の二因子の射を交換して普遍的な切断の評価で比較する。
規約：射影に left fibration 性を要求しない。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS） の切断空間の通常の極限錐の自然性。 -/
lemma transportSectionsRestriction_post (p : E ⟶ nerve I) (q : E' ⟶ nerve I)
    (f : E ⟶ E') (hf : f ≫ q = p) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction q i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction p i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportPost p q f hf).app i := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective q (nerveMap (Under.forget i))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction_evaluation]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf (nerveMap (Under.forget i)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction_evaluation,
    ← Category.assoc, whisker_exchange, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_evaluation,
    ← Category.assoc]

/-- 概要：切断から transport の end への比較は底を保つ全空間の射について自然である。
方針：切断が担う通常の錐の成分の自然性に、重み付き錐の比較の自然性を適用する。
規約：標準比較射そのものの厳密な可換性を述べる。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の全空間の比較と end の同値不変性の接続。 -/
lemma strictTransportSectionsComparison_naturality
    (p : E ⟶ nerve I) (q : E' ⟶ nerve I) (f : E ⟶ E') (hf : f ≫ q = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison p ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportPost p q f hf) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportPost p q f hf) (transportSectionsRestriction_post p q f hf)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
