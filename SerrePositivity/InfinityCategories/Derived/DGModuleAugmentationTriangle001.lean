module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationTriangleCoefficient
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcomposeTriangle
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
/-- 三点の実相 001。 -/
def dgModuleAugmentationPhase001 : Fin 3 →o Fin 2 where
  toFun i := if i = 2 then 1 else 0
  monotone' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (s : Simplex R (DGModuleFunctorResolutionObject R C E F) 2)
/-- 相 001 の候補係数は、同じ augmentation と実三角係数の後合成。 -/
lemma dgModuleAugmentationPrismMixedHom_001 :
    dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData
      dgModuleAugmentationPhase001 Finset.univ 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) =
    compose R (x := (s.obj 0).replacement.val) (y := (s.obj 2).replacement.val)
      (z := F.obj (s.obj 2).source) (n := -1)
      (dgModuleAugmentationComponent R C E F (s.obj 2)).val
      (s.map (dgModuleAugmentationSource R C E F)).triangleHom (by omega) := by
  simp [dgModuleAugmentationPrismMixedHom, dgModuleAugmentationPhase001,
    Fin.sum_univ_three, Simplex.triangleHom, Simplex.map, SimplexData.map]
/-- 候補切断和そのものの相 001 の実二次微分式。 -/
lemma dgModuleAugmentationPrismMixedHom_001_differential :
    (moduleHom R E (s.obj 0).replacement.val (F.obj (s.obj 2).source)).d (-1) 0
      (dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData
        dgModuleAugmentationPhase001 Finset.univ 0 2 (-1)
        (by decide) (by decide) (by decide) (by decide)) =
    compose R (x := (s.obj 0).replacement.val) (y := (s.obj 1).replacement.val)
      (z := F.obj (s.obj 2).source) (n := 0)
      (compose R (x := (s.obj 1).replacement.val) (y := (s.obj 2).replacement.val)
        (z := F.obj (s.obj 2).source) (n := 0)
        (dgModuleAugmentationComponent R C E F (s.obj 2)).val
        ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 1 2 (by decide)) (by omega))
      ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide)) (by omega) -
    compose R (x := (s.obj 0).replacement.val) (y := (s.obj 2).replacement.val)
      (z := F.obj (s.obj 2).source) (n := 0)
      (dgModuleAugmentationComponent R C E F (s.obj 2)).val
      ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 2 (by decide)) (by omega) := by
  rw [dgModuleAugmentationPrismMixedHom_001]
  exact dgClosedPostcomposeTriangle_differential R
    ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide))
    ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 1 2 (by decide))
    ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 2 (by decide))
    (s.map (dgModuleAugmentationSource R C E F)).triangleHom
    (dgModuleAugmentationComponent R C E F (s.obj 2)).val
    (dgModuleAugmentationComponent R C E F (s.obj 2)).property
    (s.map (dgModuleAugmentationSource R C E F)).differential_triangleHom
end SerrePositivity.InfinityCategories
