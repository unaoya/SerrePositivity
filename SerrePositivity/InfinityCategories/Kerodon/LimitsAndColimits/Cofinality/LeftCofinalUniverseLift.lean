module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy

/-!
概要：left cofinalな元の単体集合の射は、宇宙を持ち上げてもleft cofinal。
方針：反転し既存のright版を適用し、同じ写像の反転と宇宙変更の同型で戻す。
規約：大きい試験fibrationへの条件を小さいものに制限しない。
使われ方：G9-2、持ち上げたČech形状のleft cofinal性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 元のleft cofinal写像を宇宙持ち上げした同じ写像もleft cofinal。 -/
lemma isLeftCofinal_ulift {A B : SSet.{u}} (f : A ⟶ B) (hf : IsLeftCofinal f) :
    IsLeftCofinal ((SSet.uliftFunctor.{v, u}).map f) := by
  apply (isLeftCofinal_iff_isRightCofinal_op _).mpr
  exact (isRightCofinal_ulift (SSet.opFunctor.map f) hf.op).of_arrow_iso
    (Arrow.isoMk (uliftOppositeIso.{u, v} A) (uliftOppositeIso.{u, v} B) (by rfl))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
