module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalHomotopyRetract
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialFibrationHomotopy

/-!
概要：任意の trivial Kan fibration は左右 cofinal。
方針：厳密な切断を取り、同じ底の上のホモトピーを両方向に選ぶ。
規約：元の始域・終域の充填性を仮定しない。
使われ方：Kerodon Corollary 7.2.1.14（Tag 02ND） の逆方向、Corollary 7.2.1.15。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：trivial Kan fibration は底上の収縮を持つ切断を持つ。
方針：空部分から切断を選び、全射の同じ fiber 内で二つの合成を恒等射に結ぶ。
規約：両方向のホモトピーの底への像は厳密に時間に定値。
使われ方：任意の底上の関手空間の制限のホモトピー逆。 -/
lemma nonempty_cofinalSectionHomotopy_of_trivialKanFibration {A B : SSet.{u}}
    (f : A ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f] : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalSectionHomotopy f) := by
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section f
  have hsp : (𝟙 A) ≫ f = (f ≫ s) ≫ f := by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration f (𝟙 A) (f ≫ s) hsp
  obtain ⟨K, hK⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration f (f ≫ s) (𝟙 A) hsp.symm
  refine ⟨⟨s, hs, H, ?_, K, ?_⟩⟩
  · simpa only [Category.assoc, hs, Category.comp_id] using hH
  · simpa only [Category.id_comp] using hK

/-- 概要：trivial Kan fibration は left cofinal。
方針：底上の切断と収縮から全ての left fibration の検査を満たす。
規約：始域・終域は任意。
使われ方：Kerodon Corollary 7.2.1.14（Tag 02ND） の (3)⇒(1)。 -/
lemma isLeftCofinal_of_trivialKanFibration {A B : SSet.{u}} (f : A ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f := by
  obtain ⟨d⟩ := nonempty_cofinalSectionHomotopy_of_trivialKanFibration f
  exact d.isLeftCofinal

/-- 概要：trivial Kan fibration は right cofinal。
方針：底上の切断と収縮から全ての right fibration の検査を満たす。
規約：始域・終域は任意。
使われ方：Kerodon Corollary 7.2.1.14（Tag 02ND） の (3)⇒(2)。 -/
lemma isRightCofinal_of_trivialKanFibration {A B : SSet.{u}} (f : A ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f := by
  obtain ⟨d⟩ := nonempty_cofinalSectionHomotopy_of_trivialKanFibration f
  exact d.isRightCofinal

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
