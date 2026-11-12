module
public import SerrePositivity.KST.SConstruction.CofiberFamilies
public import SerrePositivity.KST.SConstruction.FullSubcomplexFunctorIsoReflection

/-! # 自明 Kan ファイブレーションによる関手同型の反映
概要：射影後に coherent に同型な二つの族を、元の族の関手同型へ持ち上げる。
方針：内部 Hom の自明ファイブレーションの h での充満忠実性を使う。
規約：射影後の厳密な等号を要求しない。使われ方：入力族の同型から全 cofiber 族へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- 自明 Kan ファイブレーションへの後合成後の関手同型を元の二つの族へ反映する。 -/
def functorIsoOfTrivialKanFibrationPostcomp {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    {f g : K ⟶ C} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ p) (g ≫ p)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  let h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration ((ihom K).map p)).isFullyFaithful
  exact h.toHoFullyFaithful.preimageIso e

end SerrePositivity.KST.SConstruction
