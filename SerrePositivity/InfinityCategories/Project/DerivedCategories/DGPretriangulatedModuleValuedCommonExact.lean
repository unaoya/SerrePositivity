module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedYonedaCommonExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorCommonExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTensorYonedaCommonIso
/-!
概要：前三角な小 dg 圏から独立の宇宙の全加群圏への任意の dg 関手は完全。
方針：共通宇宙の Yoneda と kernel tensor を合成し、実関手同型で元の作用へ移送する。
規約：Small は始域と係数圏だけ。対象宇宙の持ち上げ以外は変更しない。
使われ方：D2 G-1 e の混在宇宙の第二脚 M.toFunctor を直接接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) (C : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]

theorem dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] (F : DGFunctor R D (RightModule R C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, max (u + 1) w, max (u + 1) v w t} F) := by
  let P : Bimodule R C D := F
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYonedaCommon_isExactFunctor.{u, v, max w t} R D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorCommonNerve_isExactFunctor.{u, v, w, max (u + 1) v w t}
    R D C (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C P)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorYonedaCommonIso.{u, v, w, t} R D C P)

/-- 始域と全加群終域の対象だけを同じ宇宙へ上げた native nerve の完全性。 -/
theorem dgPretriangulatedModuleValuedFunctorLifted_isExactFunctor
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] (F : DGFunctor R D (RightModule R C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, max (u + 1) w,
      max (u + 1) v w t, max (u + 1) v w t} F)) := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max (u + 1) v w t} R D
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, max (u + 1) w, max (u + 1) v w t}
    R (_root_.SerrePositivity.DifferentialGraded.RightModule R C)
  let := dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor.{u, v, w, t} R D C F
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso d.symm).isQCatEquivalence
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (d.inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, max (u + 1) w, max (u + 1) v w t} F ≫ e.hom) :=
    inferInstance
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_lifted] at h
  simpa only [d, e, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
