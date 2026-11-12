module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationTriangleCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcomposeTriangle
/-!
概要：相 001 の候補切断和を実後合成係数へ同定し、同じ候補の二次微分式を証明する。
方針：相一の内部切断が無いことと、実閉 augmentation による三角係数の後合成を使う。
規約：任意次元の一般 HA 方程式は別工程。使われ方：全 prism の二つの混合二次境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
/-- 三点の実相 001。 -/
def dgModuleAugmentationPhase001 : Fin 3 →o Fin 2 where
  toFun i := if i = 2 then 1 else 0
  monotone' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) 2)
/-- 相 001 の候補係数は、同じ augmentation と実三角係数の後合成。 -/
lemma dgModuleAugmentationPrismMixedHom_001 :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData
      dgModuleAugmentationPhase001 Finset.univ 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 0).replacement.val) (y := (s.obj 2).replacement.val)
      (z := F.obj (s.obj 2).source) (n := -1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).val
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).triangleHom (by omega) := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom, dgModuleAugmentationPhase001,
    Fin.sum_univ_three, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map]
/-- 候補切断和そのものの相 001 の実二次微分式。 -/
lemma dgModuleAugmentationPrismMixedHom_001_differential :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj 0).replacement.val (F.obj (s.obj 2).source)).d (-1) 0
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData
        dgModuleAugmentationPhase001 Finset.univ 0 2 (-1)
        (by decide) (by decide) (by decide) (by decide)) =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 0).replacement.val) (y := (s.obj 1).replacement.val)
      (z := F.obj (s.obj 2).source) (n := 0)
      (_root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 1).replacement.val) (y := (s.obj 2).replacement.val)
        (z := F.obj (s.obj 2).source) (n := 0)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).val
        ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 1 2 (by decide)) (by omega))
      ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide)) (by omega) -
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 0).replacement.val) (y := (s.obj 2).replacement.val)
      (z := F.obj (s.obj 2).source) (n := 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).val
      ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 2 (by decide)) (by omega) := by
  rw [dgModuleAugmentationPrismMixedHom_001]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposeTriangle_differential R
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide))
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 1 2 (by decide))
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 2 (by decide))
    (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).triangleHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).property
    (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).differential_triangleHom
end SerrePositivity.InfinityCategories.Project.DerivedCategories
