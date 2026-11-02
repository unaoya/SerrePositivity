module
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalComposition
public import SerrePositivity.InfinityCategories.F1B.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedInfinity
public import SerrePositivity.InfinityCategories.HomotopyLimits.CofinalTensor
public import SerrePositivity.InfinityCategories.HomotopyLimits.NonemptyFiniteSSetProduct
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.SiftedFiniteDiagonal


/-!
概要：sifted な底から元の全有限非空反復積への対角は right cofinal。
方針：元の二項対角と、残りの元の反復対角との直積を合成する。
規約：n は因子数 n+1。底の quasicategory 性は仮定しない。
使われ方：HTT 5.5.8.11、余極限と全有限積の交換の非空の場合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- sifted な底の元の有限非空反復対角は、全因子数で right cofinal。 -/
lemma nonemptyFiniteDiagonal_isRightCofinal (B : SSet.{u}) [IsSiftedInfinity B] (n : ℕ) :
    IsRightCofinal (nonemptyFiniteDiagonal B n) := by
  induction n with
  | zero => exact isRightCofinal_id B
  | succ n ih =>
    have h := (IsSiftedInfinity.diagonal_rightCofinal (K := B)).comp
      (isRightCofinal_whiskerLeft ih B)
    have he : lift (𝟙 B) (𝟙 B) ≫ (B ◁ nonemptyFiniteDiagonal B n) =
        nonemptyFiniteDiagonal B (n + 1) := by
      rw [lift_whiskerLeft, Category.id_comp]
      rfl
    rwa [he] at h

end SerrePositivity.InfinityCategories.HomotopyLimits
