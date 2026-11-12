module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomComparisonFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan

/-!
概要：表現可能な相対 Hom の strict 比較の全パラメーターを単体集合に束ねる。
方針：各標準単体上の比較の族を次数とし、回収の自然性から相対 Hom との同型を作る。
規約：全標的を走る族の宇宙は u+1。相対 Hom の宇宙持ち上げとの厳密な同型を示す。
使われ方：面・退化を保つ比較の回収と、比較空間のホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 各標準単体上の全 Hom に自然な strict 比較を単体集合にする。 -/
def relativeHomComparisonSpace {B : SSet.{u}} (a : Over B)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) : SSet.{u + 1} where
  obj n := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomComparisonFamily a q (stdSimplex.obj n.unop)
  map f := ↾fun η ↦ η.restrict (stdSimplex.map f.unop)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro η
    change η.restrict (stdSimplex.map (𝟙 n.unop)) = η
    rw [CategoryTheory.Functor.map_id, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomComparisonFamily.restrict_id]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro η
    change η.restrict (stdSimplex.map (g.unop ≫ f.unop)) =
      (η.restrict (stdSimplex.map f.unop)).restrict (stdSimplex.map g.unop)
    rw [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomComparisonFamily.restrict_comp]

/-- 相対 Hom の全単体を、その全標的への前合成の比較に写す。 -/
def relativeHomComparisonSpaceTo {B : SSet.{u}} (a : Over B)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom) ⟶
      relativeHomComparisonSpace a q where
  app _ := ↾fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyOfMap (SSet.yonedaEquiv.symm f.down)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro f
    change _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyOfMap
      (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom).map α f.down)) =
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyOfMap (SSet.yonedaEquiv.symm f.down)).restrict
        (stdSimplex.map α.unop)
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyOfMap_restrict, SSet.yonedaEquiv_symm_naturality_left]
    simp only [Quiver.Hom.op_unop]

/-- 比較の各単体を恒等射で評価して相対 Hom の単体へ戻す。 -/
def relativeHomComparisonSpaceFrom {B : SSet.{u}} (a : Over B)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    relativeHomComparisonSpace a q ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom) where
  app _ := ↾fun η ↦ ULift.up (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyMap η))
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro η
    apply ULift.ext
    change SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyMap (η.restrict (stdSimplex.map α.unop))) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom).map α
          (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyMap η))
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyMap_restrict, ← SSet.yonedaEquiv_naturality]
    simp only [Quiver.Hom.op_unop]

/-- 恒等射での回収は、面・退化を含む比較空間全体と相対 Hom の厳密な同型。 -/
def relativeHomComparisonSpaceIso {B : SSet.{u}} (a : Over B)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom) ≅
      relativeHomComparisonSpace a q where
  hom := relativeHomComparisonSpaceTo a q
  inv := relativeHomComparisonSpaceFrom a q
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    change SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyMap
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyOfMap (SSet.yonedaEquiv.symm f.down))) = f.down
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyMap_ofMap, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro η
    change _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyOfMap
      (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyMap η))) = η
    rw [Equiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonFamilyOfMap_map]

/-- 表現可能な相対 Hom の strict 比較空間は Kan 複体。 -/
instance relativeHomComparisonSpace_kanComplex {B : SSet.{u}} (a : Over B)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) : KanComplex (relativeHomComparisonSpace a q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (relativeHomComparisonSpaceIso a q)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
