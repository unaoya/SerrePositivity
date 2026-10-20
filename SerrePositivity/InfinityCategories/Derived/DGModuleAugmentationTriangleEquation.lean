module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationHomotopyNaturality
public import SerrePositivity.InfinityCategories.Derived.DGHomotopyNaturalTriangle
public import SerrePositivity.InfinityCategories.DGNerve.Triangle
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (s : Simplex R (DGModuleFunctorResolutionObject R C E F) 2)
/-- 相 011 の同じ実補正係数。 -/
def dgModuleAugmentationTriangle011Homotopy :
    GradedHom R (s.obj 0).replacement.val (F.obj (s.obj 2).source) (-1) :=
  compose R (x := (s.obj 0).replacement.val) (y := (s.obj 2).replacement.val)
    (z := F.obj (s.obj 2).source) (n := -1) (dgModuleAugmentationComponent R C E F (s.obj 2)).val
    (s.map (dgModuleAugmentationSource R C E F)).triangleHom (by omega) -
  compose R (x := (s.obj 0).replacement.val) (y := (s.obj 1).replacement.val)
    (z := F.obj (s.obj 2).source) (n := -1)
    (dgModuleAugmentationHomotopyComponent R C E F (s.obj 1) (s.obj 2) 0
      (s.edgeHom 1 2 (by decide)))
    ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide)) (by omega)
/-- 同じ実補正係数の微分は、混合三角形の同じ実二辺の合成の差。 -/
lemma dgModuleAugmentationTriangle011Homotopy_differential :
    (moduleHom R E (s.obj 0).replacement.val (F.obj (s.obj 2).source)).d (-1) 0
      (dgModuleAugmentationTriangle011Homotopy R C E F s) =
    compose R (x := (s.obj 0).replacement.val) (y := F.obj (s.obj 1).source)
      (z := F.obj (s.obj 2).source) (n := 0)
      ((s.map (dgModuleAugmentationTarget R C E F)).edgeHom 1 2 (by decide))
      (compose R (x := (s.obj 0).replacement.val) (y := (s.obj 1).replacement.val)
        (z := F.obj (s.obj 1).source) (n := 0) (dgModuleAugmentationComponent R C E F (s.obj 1)).val
        ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide)) (by omega))
      (by omega) -
    compose R (x := (s.obj 0).replacement.val) (y := (s.obj 2).replacement.val)
      (z := F.obj (s.obj 2).source) (n := 0) (dgModuleAugmentationComponent R C E F (s.obj 2)).val
      ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 2 (by decide)) (by omega) := by
  exact dgHomotopyNaturalTriangle_differential R
    ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 1 (by decide))
    ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 1 2 (by decide))
    ((s.map (dgModuleAugmentationSource R C E F)).edgeHom 0 2 (by decide))
    (s.map (dgModuleAugmentationSource R C E F)).triangleHom
    ((s.map (dgModuleAugmentationTarget R C E F)).edgeHom 1 2 (by decide))
    (dgModuleAugmentationComponent R C E F (s.obj 1)).val
    (dgModuleAugmentationComponent R C E F (s.obj 2)).val
    (dgModuleAugmentationHomotopyComponent R C E F (s.obj 1) (s.obj 2) 0
      (s.edgeHom 1 2 (by decide)))
    (dgModuleAugmentationComponent R C E F (s.obj 2)).property
    ((s.map (dgModuleAugmentationSource R C E F)).edgeCycle 0 1 (by decide)).property
    (s.map (dgModuleAugmentationSource R C E F)).differential_triangleHom
    (dgModuleAugmentationHomotopyComponent_closed_zero R C E F (s.obj 1) (s.obj 2)
      (s.edgeHom 1 2 (by decide)) (s.edgeCycle 1 2 (by decide)).property)
end SerrePositivity.InfinityCategories
