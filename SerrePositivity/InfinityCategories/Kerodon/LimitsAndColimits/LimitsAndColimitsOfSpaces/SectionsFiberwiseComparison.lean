module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportSectionsNaturality

/-!
概要：cospan・塔・離散圏上の left fibration の fiber ごとの同値は切断空間の同値を誘導する。
方針：切断空間と transport の end の標準比較の自然性と、end の同値不変性を使う。
規約：比較は同じ底を保つ全空間の実際の射から誘導する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の coherent な錐と表現可能な図式の切断模型の比較。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：transport への標準比較が同値な二射影では fiber ごとの同値が切断空間の同値を誘導する。
方針：標準比較の可換四角形の残る三辺の同値性を二対三で使う。
規約：標準比較の同値性 hp・hq は、具体的な添字圏に適用する前段の入力。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の具体的な極限の切断模型の比較。 -/
lemma simplicialSectionsMap_homotopyEquivalence_of_transportComparisons
    {I : Type u} [SmallCategory I] {E E' : SSet.{u}}
    (p : E ⟶ nerve I) (q : E' ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf ((nerveEquiv (C := I)).symm i)))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison p))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex q
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
    apply hq.isQCatEquivalence.cancel_right
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictTransportSectionsComparison_naturality]
    exact hp.isQCatEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportPost_end_homotopyEquivalence p q f hf h).isQCatEquivalence
  exact he.isSimplicialHomotopyEquivalence

/-- 概要：cospan 上の left fibration 間の fiber ごとの同値は切断空間のホモトピー同値を誘導する。
方針：cospan の標準比較の同値性を一般の可換四角形の判定へ渡す。
規約：全空間の射 f の fibration 性や自明 Kan fibration 性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の引き戻しの錐の模型の比較。 -/
lemma simplicialSectionsMap_cospan_homotopyEquivalence {E E' : SSet.{u}}
    (p : E ⟶ nerve (AsSmall.{u} WalkingCospan))
    (q : E' ⟶ nerve (AsSmall.{u} WalkingCospan)) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf
      ((nerveEquiv (C := AsSmall.{u} WalkingCospan)).symm i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) :=
  simplicialSectionsMap_homotopyEquivalence_of_transportComparisons p q f hf h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison_cospan_homotopyEquivalence p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison_cospan_homotopyEquivalence q)

/-- 概要：塔上の left fibration 間の fiber ごとの同値は切断空間のホモトピー同値を誘導する。
方針：塔の標準比較の同値性を一般の可換四角形の判定へ渡す。
規約：添字は AsSmall.{u} ℕᵒᵖ とし、f 自身の充填性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の塔の錐の模型の比較。 -/
lemma simplicialSectionsMap_tower_homotopyEquivalence {E E' : SSet.{u}}
    (p : E ⟶ nerve (AsSmall.{u} ℕᵒᵖ)) (q : E' ⟶ nerve (AsSmall.{u} ℕᵒᵖ))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf
      ((nerveEquiv (C := AsSmall.{u} ℕᵒᵖ)).symm i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) :=
  simplicialSectionsMap_homotopyEquivalence_of_transportComparisons p q f hf h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison_tower_homotopyEquivalence p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison_tower_homotopyEquivalence q)

/-- 概要：離散圏上の left fibration 間の fiber ごとの同値は切断空間のホモトピー同値を誘導する。
方針：離散の標準比較の厳密な同型性を一般の可換四角形の判定へ渡す。
規約：添字の有限性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の積の錐の模型の比較。 -/
lemma simplicialSectionsMap_discrete_homotopyEquivalence {J : Type u} {E E' : SSet.{u}}
    (p : E ⟶ nerve (Discrete J)) (q : E' ⟶ nerve (Discrete J))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf
      ((nerveEquiv (C := Discrete J)).symm i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison_discrete_isIso p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictTransportSectionsComparison_discrete_isIso q
  exact simplicialSectionsMap_homotopyEquivalence_of_transportComparisons p q f hf h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso _)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
