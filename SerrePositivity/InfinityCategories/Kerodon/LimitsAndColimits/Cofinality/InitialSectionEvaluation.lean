module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianSectionFamilies
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialSectionTransport

/-!
概要：始対象での cocartesian section の fiber 評価に切断を構成する。
方針：fiber 全体をパラメータとする図式を始対象から延長して curry する。
規約：切断は単体集合の射。境界を固定する持ち上げ性は別の課題。
使われ方：一般の strict transport の fiber 比較。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：始対象での評価は単体集合の射として切断を持つ。
方針：始対象の fiber の包含を、全 fiber をパラメータとして cocartesian に延長する。
規約：底は quasicategory、射影は cocartesian fibration。
使われ方：評価の任意のパラメータの族に対する全射性。 -/
lemma exists_kanCocartesianSectionsEvaluate_section {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (a.app (Opposite.op ⦋0⦌) v) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a,
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p a v = 𝟙 _ := by
  obtain ⟨F, hFp, hFi, hFc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.exists_kanInitialSectionTransport p a v hv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (a.app (Opposite.op ⦋0⦌) v)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _)
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsCurry F hFp hFc
  refine ⟨s, ?_⟩
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (a.app (Opposite.op ⦋0⦌) v))).1
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_evaluate,
    show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry s = F from _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_curry F hFp hFc,
    hFi, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
