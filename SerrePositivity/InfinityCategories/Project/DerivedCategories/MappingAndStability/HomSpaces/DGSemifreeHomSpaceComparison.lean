module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleOutputResolutionSpaceIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeHomSpaceAugmentation
/-!
概要：固定入力の D(R) 値 Hom の基礎空間を、元の同じ全 Hom の空間値関手と比較する。
方針：同じ実 augmentation の全関手同型を実入力へ制限し、反変側は実反対 nerve を経る。
規約：全単体族の比較同型。元の導来圏の F1 Hom 関手との同定は別工程。
使われ方：β5 の D(R) 値 Hom と空間値 Hom の自然な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 同じ実 augmentation による、固定始域の全空間値関手の比較同型。 -/
def dgSemifreeDerivedHomTargetSpaceIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity R D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetSpaceInfinity R D P) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionSpaceComparisonIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleDG R D P))
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))))
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) PUnit.{1}
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleDG R D P)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleInfinity R D P := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift_up]
    rfl
  simp only [← Category.assoc, ← Functor.map_comp] at e
  rw [h1] at e
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleInclusionInfinity,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetSpaceInfinity, Functor.map_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve] using e
/-- 同じ実 augmentation による、dg 反対模型上の固定終域 Hom の全関手比較同型。 -/
def dgSemifreeDerivedHomSourceSpaceIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceDGopInfinity R D P) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity R D))
      (((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleInfinity R D P) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionSpaceComparisonIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleDG R D P))
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ)))
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ PUnit.{1}
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleDG R D P)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleInfinity R D P := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift_up]
    rfl
  simp only [← Category.assoc, ← Functor.map_comp] at e
  rw [h1] at e
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceDGopInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleInclusionInfinity,
    Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve] using e
/-- 実反対 ∞ 圏上の D(R) 値 Hom と元の全 Hom の、全空間値関手の比較同型。 -/
def dgSemifreeDerivedHomContravariantSpaceIso (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantSpaceInfinity R D Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomContravariantSpaceInfinity R D Q) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgSemifreeDerivedHomSourceSpaceIso R D Q)
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantSpaceInfinity,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomContravariantSpaceInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedContravariantHomInfinity,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomContravariantModuleInfinity, Functor.map_comp, Category.assoc] using e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
