module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorClosedCosliceFiber
/-!
概要：実 coslice の合成比較の fiber 射を、同じ合成 Hom 鎖写像の左 Hom 作用へ同定する。
方針：後合成と閉前合成の全単体等式を結び、同じ鎖写像作用の厳密な合成則を使う。
規約：各因子の準同型性を要求せず、合成した同じ Hom 鎖写像の準同型性だけを使う。
使われ方：Hom 単位の実 coslice 比較が全 fiber で同値であることの証明。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (x : D) (q : E) (y : D)
  (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x))
/-- 同じ dg 関手の実 coslice fiber の左 Hom 表示は、同じ Hom 鎖写像の作用。 -/
lemma dgFunctorCosliceLeftMap_eq_chainMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCosliceLeftMap R F x y = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E (F.map x y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal_injective n
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCosliceLeftMap_simplex R F x y t).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap_functor_val R F x y t).symm
/-- 同じ実合成比較の fiber 射を、標準左 Hom の同型で移した写像。 -/
def dgFunctorClosedCosliceLeftMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorClosedCosliceFiber R F x q y s ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))).inv
/-- 同じ実合成比較の左 Hom 表示は、元の二つの実左 Hom 写像の合成。 -/
lemma dgFunctorClosedCosliceLeftMap_factorization :
    dgFunctorClosedCosliceLeftMap R F x q y s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCosliceLeftMap R F x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap R E (F.obj x) q (F.obj y) s := by
  rw [dgFunctorClosedCosliceLeftMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorClosedCosliceFiber_factorization]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCosliceLeftMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap, Category.assoc,
    Iso.inv_hom_id_assoc]
/-- 同じ実合成比較の左 Hom 表示は、同じ合成 Hom 鎖写像の作用に等しい。 -/
lemma dgFunctorClosedCosliceLeftMap_eq_chainMap :
    dgFunctorClosedCosliceLeftMap R F x q y s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E (F.map x y ≫
        eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj y))) := by
  rw [dgFunctorClosedCosliceLeftMap_factorization, dgFunctorCosliceLeftMap_eq_chainMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap_eq_chainMap]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap_comp R _ _).symm
lemma dgFunctorClosedCosliceFiber_isQCatEquivalence
    [QuasiIso (F.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj y)))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorClosedCosliceFiber R F x q y s) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))
  have H : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgFunctorClosedCosliceLeftMap R F x q y s) := by
    rw [dgFunctorClosedCosliceLeftMap_eq_chainMap]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap_isQCatEquivalence R D E _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorClosedCosliceFiber R F x q y s ≫ f.inv)) at H
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso f.symm).isQCatEquivalence.cancel_right
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.cancel_left H)
lemma dgFunctorClosedCosliceRawFiber_isQCatEquivalence
    [QuasiIso (F.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj y)))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorClosedCosliceMap R F x q s) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorClosedCosliceMap_projection R F x q s) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) := by
  let e := eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.cancel_right
    (dgFunctorClosedCosliceFiber_isQCatEquivalence R F x q y s)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
