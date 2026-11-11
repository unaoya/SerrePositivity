module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPostUncurry
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorSquarePost

/-!
概要：底上の始域・標的の同型で移した相対 Hom の族の評価を厳密に計算する。
方針：始域の逆同型の前合成と、標的の順同型の後合成へ展開する。
規約：任意のパラメーターを保ち、充填性を要求しない。
使われ方：unstraightening の底変換同型による、実際の相対引き戻し作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 全空間の底上の同型による相対 Hom の移送は、評価後に元の共役として読める。 -/
lemma relativeFunctorOverIso_uncurry {B T : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p')
    (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom a.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverIso ea ep).hom) =
      (ea.inv.left ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry g ≫ ep.hom.left := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverIso_hom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPost_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_uncurry, Category.assoc]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
