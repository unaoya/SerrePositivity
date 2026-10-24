module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.PinchedComposition
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceIntervalNaturality
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFamilyInvariance

/-!
# 元の pinched 後合成が表す任意パラメータの全族

概要：同じ選ばれた pinched 後合成は、区間模型で元の射の後合成を表す。
方針：元の比較二胞体を任意 K で制限し、区間後合成の全族公式を使う。
規約：指定された postcompose と comparison を変えない。
使われ方：実半自由 retract の後合成を含む導来 Hom 比較の全族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

lemma pinchedPostcompose_family {K C : SSet.{u}} [Quasicategory C]
    {x y z : C.obj (Opposite.op (SimplexCategory.mk 0))}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj C) ⟶ HomotopyCategory.mk z)
    (f : K ⟶ pinchedHom x y) :
    intervalFamilyHom (f ≫ PinchedInterval.postcompose x δ ≫
      SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace x z) =
    intervalFamilyHom (f ≫ SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace x y) ≫ constantFunctorHomMap K δ := by
  have H := FunctorIso.simplicialHomotopy
    (PinchedInterval.liftMapComparisonIso (intervalPostcompose x δ))
  have h := intervalFamilyHom_eq_of_homotopy (functorHomotopyPrecomp H f)
  calc
    _ = intervalFamilyHom (f ≫ (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace x y ≫
        intervalPostcompose x δ)) := by
      simpa only [PinchedInterval.postcompose, Category.assoc] using h
    _ = _ := by rw [← Category.assoc, intervalPostcompose_family]

lemma pinchedPostcompose_intervalFamily {K C : SSet.{u}} [Quasicategory C]
    {x y z : C.obj (Opposite.op (SimplexCategory.mk 0))}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj C) ⟶ HomotopyCategory.mk z)
    (f : K ⟶ pinchedHom x y) :
    intervalFamilyHom (f ≫ PinchedInterval.postcompose x δ ≫
      pinchedHomToIntervalMappingSpace x z) =
    intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫ constantFunctorHomMap K δ := by
  simpa only [pinchedInterval_comparison_eq] using pinchedPostcompose_family δ f

end SerrePositivity.EInfinity.ComplexLimits
