module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalTensor
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NonemptyFiniteSSetProduct
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.HomotopyLimitsPresentableSiftedFiniteDiagonal


/-!
概要：sifted な底から元の全有限非空反復積への対角は right cofinal。
方針：元の二項対角と、残りの元の反復対角との直積を合成する。
規約：n は因子数 n+1。底の quasicategory 性は仮定しない。
使われ方：HTT 5.5.8.11、余極限と全有限積の交換の非空の場合。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- sifted な底の元の有限非空反復対角は、全因子数で right cofinal。 -/
lemma nonemptyFiniteDiagonal_isRightCofinal (B : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n) := by
  induction n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_id B
  | succ n ih =>
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity.diagonal_rightCofinal (K := B)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_whiskerLeft ih B)
    have he : lift (𝟙 B) (𝟙 B) ≫ (B ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B (n + 1) := by
      rw [lift_whiskerLeft, Category.id_comp]
      rfl
    rwa [he] at h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
