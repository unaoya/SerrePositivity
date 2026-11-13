module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceIntervalNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
/-!
概要：実 pinched Hom 族の後合成を、同じ関手圏の後合成へ端点の同型ごと移す。
方針：実区間比較の厳密な自然性と関手圏の後合成の計算を使う。
規約：有限性・充填性を仮定しない。使われ方：dg 屋根の実評価方程式の正規化。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 実 pinched Hom 族の像は、同じ関手圏の後合成を定値端点の同型で共役したもの。 -/
lemma pinchedFamilyHom_postcomp {K X Y : SSet.{u}} (F : X ⟶ Y)
    {x y : X _⦋0⦌} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom ((f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K x F).inv ≫
        (hoFunctor.map ((ihom K).map F)).toFunctor.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)) ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K y F).hom := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pinchedHomToIntervalMappingSpace_naturality]
  simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom
    (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) F
/-- 端点の三同型による共役は、同じ分母評価方程式を保つ。 -/
lemma roofConjugatedEvaluation_fac {C : Type v} [Category.{w} C]
    {q x y q' x' y' : C} (i : q ≅ q') (j : x ≅ x') (k : y ≅ y')
    (d : q ⟶ x) (e : x ⟶ y) (n : q ⟶ y) (h : d ≫ e = n) :
    (i.inv ≫ d ≫ j.hom) ≫ (j.inv ≫ e ≫ k.hom) = i.inv ≫ n ≫ k.hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg (fun a => i.inv ≫ a ≫ k.hom) h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
