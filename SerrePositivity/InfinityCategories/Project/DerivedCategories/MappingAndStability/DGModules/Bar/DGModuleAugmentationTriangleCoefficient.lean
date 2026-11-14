module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationTriangleEquation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationPrismBoundary
/-!
概要：相 011 の実候補切断和を、同じ実三角形の補正係数と厳密に同定する。
方針：三点の内部和を一項へ簡約し、左右切断の有限濃度と次数を照合する。
規約：この二次比較は一般 HA 方程式の代用ではない。使われ方：全 prism の二次境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
/-- 三点の実相 011。 -/
def dgModuleAugmentationPhase011 : Fin 3 →o Fin 2 where
  toFun i := if i = 0 then 0 else 1
  monotone' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) 2)
/-- 候補切断和の相 011 の係数は、同じ実三角形の補正係数。 -/
lemma dgModuleAugmentationPrismMixedHom_011 :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData
      dgModuleAugmentationPhase011 Finset.univ 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTriangle011Homotopy R C E F s := by
  have h₁ : ({x : Fin 3 | 1 < x} : Finset (Fin 3)) = {2} := by decide
  have h₂ : ({x : Fin 3 | 1 ≤ x} : Finset (Fin 3)) = {1, 2} := by decide
  have h₃ : ({x : Fin 3 | x ≤ 1} : Finset (Fin 3)) = {0, 1} := by decide
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCut,
    dgModuleAugmentationPhase011, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTriangle011Homotopy, Fin.sum_univ_three,
    h₁, h₂, h₃, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeHom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map]
  simp only [sub_eq_add_neg]
  congr 3
/-- 候補切断和そのものの相 011 の二次微分式。 -/
lemma dgModuleAugmentationPrismMixedHom_011_differential :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj 0).replacement.val (F.obj (s.obj 2).source)).d (-1) 0
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData
        dgModuleAugmentationPhase011 Finset.univ 0 2 (-1)
        (by decide) (by decide) (by decide) (by decide)) =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 0).replacement.val) (y := F.obj (s.obj 1).source)
      (z := F.obj (s.obj 2).source) (n := 0)
      ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F)).edgeHom 1 2 (by decide))
      (_root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 0).replacement.val) (y := (s.obj 1).replacement.val)
        (z := F.obj (s.obj 1).source) (n := 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 1)).val
        ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide)) (by omega))
      (by omega) -
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 0).replacement.val) (y := (s.obj 2).replacement.val)
      (z := F.obj (s.obj 2).source) (n := 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).val
      ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 2 (by decide)) (by omega) := by
  rw [dgModuleAugmentationPrismMixedHom_011]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTriangle011Homotopy_differential R C E F s
end SerrePositivity.InfinityCategories.Project.DerivedCategories
