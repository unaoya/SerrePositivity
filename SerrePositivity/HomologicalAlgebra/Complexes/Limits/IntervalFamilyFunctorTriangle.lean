module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.IntervalFamilyFunctorPrecomposition

/-!
概要：指定された実屋根評価方程式を同じ関手で送る。
方針：全区間族と定値射の後合成公式を使い、端点比較を相殺する。
規約：任意のパラメータと同じ二つの射を保つ。
使われ方：元の正規化 frame の屋根評価を既存 D(R) へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalClosed _root_.SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

lemma intervalFamilyFunctorMap_triangle {K C D : SSet.{u}} (F : C ⟶ D)
    {p x y : C _⦋0⦌}
    (a : (HomotopyCategory.mk p : hoFunctor.obj C) ⟶ HomotopyCategory.mk x)
    (b : (HomotopyCategory.mk p : hoFunctor.obj C) ⟶ HomotopyCategory.mk y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom g = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K ((hoFunctor.map F).toFunctor.map a) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K ((hoFunctor.map F).toFunctor.map b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_postcomp K F a,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_postcomp K F b]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K p F).inv ≫
    (hoFunctor.map ((ihom K).map F)).toFunctor.map f ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K y F).hom) h

end SerrePositivity.ComplexLimits
