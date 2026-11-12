module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportSectionsLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanSingleFibrationComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.TowerComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.DiscreteComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportThinRestriction

/-!
概要：cospan・塔・離散圏上の left fibration の切断空間と strict transport の homotopy 極限の比較。
方針：切断空間が担う通常の極限錐に、既に証明した Bousfield–Kan 比較を適用する。
規約：元の豊穣 Hom 図式との比較はこの段階では含めない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の coherent な錐の切断模型の rectification。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：通常の圏上の射影の切断空間から strict transport の Bousfield–Kan end への標準比較。
方針：切断空間が担う通常の極限錐に標準の錐の比較射を適用する。
規約：定義には left fibration 性や比較の同値性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断模型から strict な係数模型への射。 -/
noncomputable def strictTransportSectionsComparison {I : Type u} [SmallCategory I]
    {E : SSet.{u}} (p : E ⟶ nerve I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p)

/-- 概要：cospan 上の left fibration の切断空間と strict transport の homotopy 極限は同値。
方針：薄い圏の strict transport の構造射の fibration 性を一脚の比較の定理へ渡す。
規約：p の left fibration 性以外の充填仮定は追加しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の引き戻しの coherent な錐の切断模型。 -/
lemma strictTransportSectionsComparison_cospan_homotopyEquivalence {E : SSet.{u}}
    (p : E ⟶ nerve (AsSmall.{u} WalkingCospan)) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (strictTransportSectionsComparison p) := by
  have : (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_inverse
  have : Quiver.IsThin (AsSmall.{u} WalkingCospan) := fun i j =>
    ⟨fun f g => (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan).map_injective
      (Subsingleton.elim _ _)⟩
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p
  have : KanComplex (T.obj (AsSmall.up.obj WalkingCospan.one)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport_kanComplex p _
  have : KanComplex (T.obj (AsSmall.up.obj WalkingCospan.right)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport_kanComplex p _
  have : Fibration (T.map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap_fibration_of_thin p _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence T
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsConeIsLimit p)

/-- 概要：塔上の left fibration の切断空間と strict transport の homotopy 極限は同値。
方針：strict transport の零段の Kan 性と隣接写像の fibration 性を塔の比較へ渡す。
規約：添字は AsSmall.{u} ℕᵒᵖ で固定する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の塔の coherent な錐の切断模型。 -/
lemma strictTransportSectionsComparison_tower_homotopyEquivalence {E : SSet.{u}}
    (p : E ⟶ nerve (AsSmall.{u} ℕᵒᵖ)) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (strictTransportSectionsComparison p) := by
  have : (AsSmall.down : AsSmall.{u} ℕᵒᵖ ⥤ ℕᵒᵖ).IsEquivalence :=
    (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ).isEquivalence_inverse
  have : Quiver.IsThin (AsSmall.{u} ℕᵒᵖ) := fun i j =>
    ⟨fun f g => (AsSmall.down : AsSmall.{u} ℕᵒᵖ ⥤ ℕᵒᵖ).map_injective
      (Subsingleton.elim _ _)⟩
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p
  have : KanComplex (T.obj (AsSmall.up.obj (Opposite.op 0))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport_kanComplex p _
  have : ∀ n : ℕ, Fibration (T.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) :=
    fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap_fibration_of_thin p _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_tower_homotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsConeIsLimit p)

/-- 概要：離散圏上の射影の切断空間から strict transport の Bousfield–Kan end への比較は同型。
方針：離散の標準重みの終対象性と切断空間の通常の極限性を使う。
規約：left fibration 性も係数の Kan 性も添字の有限性も要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の積の切断模型の厳密な比較。 -/
lemma strictTransportSectionsComparison_discrete_isIso {J : Type u} {E : SSet.{u}}
    (p : E ⟶ nerve (Discrete J)) : IsIso (strictTransportSectionsComparison p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_isIso_of_isTerminalWeight _ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.discreteBousfieldKanWeight_isTerminal
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsConeIsLimit p)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
