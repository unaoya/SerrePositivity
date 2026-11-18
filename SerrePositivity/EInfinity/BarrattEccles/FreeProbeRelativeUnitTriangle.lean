module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeUnitWeak
/-!
概要：局所化源での元の単位比較の全族等式を、実 U 像の前合成式へ戻す。
方針：同じ区間比較の自然性と元の前合成族公式を使う。
規約：元の単位・実 U・元の全要素族を保持する。
使われ方：標準単位の両端輸送後の全族三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：元の実単位の定値族と実 U 全族の合成は同じ複体基準族。
方針：既存の全族等式を同じ区間前合成公式で書き直す。
規約：全パラメータの射の等式。使われ方：標準単位の全族判定への輸送。 -/
lemma freeProbeRelativeUnit_forget_family_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (nerve (freeProbeRelativeElementIndex A X B))
        (freeProbeRelativeUnitHom A X) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeElementPinchedMap A X B ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (cAlgForgetDerived A) _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeUnitReference A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  have h := freeProbeRelativeUnitIntervalMap_family A X B
  rw [freeProbeRelativeUnitIntervalMap, Category.assoc, ← Category.assoc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (cAlgForgetDerived A) _ _),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pinchedHomToIntervalMappingSpace_naturality, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles
