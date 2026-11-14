module


public meta import SerrePositivity.Util.Citation
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

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.3.4.6" (partial := special) "仮定：単体集合の射が自明 Kan ファイブレーション（Lean が強い：弱ホモトピー同値のうち自明 Kan の場合。底の Kan 性は要求しない）。結論：左共終性（その場合に HA と一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_trivialKanFibration
attribute [cite HA "2.3.4.7" (partial := special) "仮定：準圏内の余極限余錐と添字への自明 Kan ファイブレーション（Lean が強い：弱ホモトピー同値を自明 Kan に限定。図式の辺が同値であることは要求しない）。結論：引き戻した余錐の余極限性（その場合に HA と一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration
attribute [cite HTT "4.1.3.2" (partial := special) "仮定：デカルトファイブレーション p の全頂点繊維が弱可縮（Lean が強い：p が右ファイブレーションで、デカルトファイブレーションの instance がある）。結論：同じ p に対する自明 Kan ファイブレーションの判定を直ちに共終性の宣言に適用すると p は共終（一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration
