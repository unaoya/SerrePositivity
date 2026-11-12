module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCommonLiftIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseExactFunctorLift
/-!
概要：前三角な小 dg 圏の Yoneda は任意の共通対象宇宙の nerve 上で完全。
方針：既存の共通宇宙 Yoneda をさらに持ち上げ、始域の上げ下げの実同型で移送する。
規約：全加群圏の Small 仮定を課さず、既存の完全性宣言を保持する。
使われ方：混在宇宙の加群値 dg 関手を kernel tensor と比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

theorem dgPretriangulatedYonedaCommon_isExactFunctor [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, max (u + 1) v, max (u + 1) v t}
      (_root_.SerrePositivity.DifferentialGraded.dgYoneda R D)) := by
  let L := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} R D).comp (dgYoneda R D)
  let I := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonLiftIso.{u, v, max (u + 1) v, t} R D
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso I).isQCatEquivalence
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_ulift.{max (u + 1) v, max (u + 1) v t}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_isExactFunctor R D)
  have hf : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) v} R D).comp L = dgYoneda R D := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro x y
    simp only [L, EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown,
      _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, Category.id_comp, Category.comp_id, eqToHom_refl]
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_comp.{u, v, max (u + 1) v, max (u + 1) v, t}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) v} R D) L
  rw [hf] at hc
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (I.hom ≫
      (SSet.uliftFunctor.{max (u + 1) v t, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)) :=
    inferInstance
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, max (u + 1) v, max (u + 1) v t}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) v} R D) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) v, max (u + 1) v t} L) at h
  rwa [hc] at h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
