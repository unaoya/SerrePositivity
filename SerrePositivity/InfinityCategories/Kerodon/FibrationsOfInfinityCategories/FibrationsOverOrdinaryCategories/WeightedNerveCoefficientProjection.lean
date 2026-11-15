module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedNerveCoefficients

/-!
概要：パラメータを射影した同じweighted係数は、元のBK入力の射列への制限。
方針：既存の直積持ち上げと第一射影の合成則を成分ごとに適用する。
規約：IS-W2 D01の既存構成の射影・自然性則。全単体と元の射列を保持。
使われ方：Kerodon 5.3.3、native Tot錐の同じ局所セルの識別。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}}

/-- パラメータ第一射影からの同じweighted係数は、元の入力のprefix制限。 -/
theorem weightedNerveCoefficients_fst (B : SSet.{u}) (φ : bousfieldKanWeight I ⟶ H)
    {n : ℕ} (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ B) :
    weightedNerveCoefficients
        (fst (bousfieldKanWeight I) ((Functor.const I).obj B) ≫ φ) σ a =
      prefixOverWeight σ ≫ Functor.whiskerLeft σ φ := by
  apply NatTrans.ext
  funext j
  change (lift ((prefixOverWeight σ).app j) _ ≫
      (fst _ _ ≫ φ.app (σ.obj j))) = (prefixOverWeight σ).app j ≫ φ.app (σ.obj j)
  rw [← Category.assoc, lift_fst]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
