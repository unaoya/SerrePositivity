module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCommonMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory
/-!
概要：混在宇宙の dg 関手の共通 nerve 写像は零頂点を保存する。
方針：native nerve の零保存を、対象宇宙比較の実同型で共役する。
規約：始域・終域に Small や安定性を仮定しない。
使われ方：全加群間および前三角始域の混在宇宙の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgNerveCommonMap_preservesZeroVertices (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, w, t} F) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_lifted]
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max u v w t} R D
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, w, max u v w t} R E
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso d).isQCatEquivalence
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e.symm).isQCatEquivalence
  intro x hx
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := e.inv) _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} F) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := d.hom) x hx))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
