module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationHomotopyNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomotopyNaturalTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle
/-!
概要：同じ実分解二単体に対し、相 011 の混合二次係数とその実微分方程式を構成する。
方針：元の同じ三角係数へ、後辺の比較 cochain と前辺の実出力の合成を引く。
規約：候補切断和との同定・一般 HA 方程式は別工程。使われ方：augmentation prism の二次検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) 2)
/-- 相 011 の同じ実補正係数。 -/
def dgModuleAugmentationTriangle011Homotopy :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj 0).replacement.val (F.obj (s.obj 2).source) (-1) :=
  _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 0).replacement.val) (y := (s.obj 2).replacement.val)
    (z := F.obj (s.obj 2).source) (n := -1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).val
    (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).triangleHom (by omega) -
  _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj 0).replacement.val) (y := (s.obj 1).replacement.val)
    (z := F.obj (s.obj 2).source) (n := -1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj 1) (s.obj 2) 0
      (s.edgeHom 1 2 (by decide)))
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide)) (by omega)
/-- 同じ実補正係数の微分は、混合三角形の同じ実二辺の合成の差。 -/
lemma dgModuleAugmentationTriangle011Homotopy_differential :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj 0).replacement.val (F.obj (s.obj 2).source)).d (-1) 0
      (dgModuleAugmentationTriangle011Homotopy R C E F s) =
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
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyNaturalTriangle_differential R
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide))
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 1 2 (by decide))
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeHom 0 2 (by decide))
    (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).triangleHom
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F)).edgeHom 1 2 (by decide))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 1)).val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj 1) (s.obj 2) 0
      (s.edgeHom 1 2 (by decide)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj 2)).property
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).edgeCycle 0 1 (by decide)).property
    (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)).differential_triangleHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent_closed_zero R C E F (s.obj 1) (s.obj 2)
      (s.edgeHom 1 2 (by decide)) (s.edgeCycle 1 2 (by decide)).property)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
