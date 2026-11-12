module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativePinchedPrismActualCoefficients
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedPrismPhase

/-! 元 gluing augmentation prism の始終対象を、同じ元対象の augmentation の二端へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y) _⦋n⦌)

abbrev dgGluingNativePinchedPrismSimplex (β : Fin (n + 1) →o Fin 2) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
    (s.val.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)

lemma dgGluingNativePinchedPrism_target (β : Fin (n + 1) →o Fin 2) :
    (dgGluingNativePinchedPrismSimplex R C D M s β).obj (Fin.last (n + 1)) =
      M.rightAt Y.right := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R D (RightModule R C) M.toFunctor
    (s.val.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)).toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)).obj
    (Fin.last (n + 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_one R D (RightModule R C) M.toFunctor _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last β)]
  change M.rightAt (s.val.obj (Fin.last (n + 1))).right = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s]

lemma dgGluingNativePinchedPrism_source_zero (β : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hβ : β i = 0) :
    (dgGluingNativePinchedPrismSimplex R C D M s β).obj i.castSucc = _root_.SerrePositivity.DifferentialGraded.representable R X.left := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R D (RightModule R C) M.toFunctor
    (s.val.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)).toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)).obj
    i.castSucc = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_zero R D (RightModule R C) M.toFunctor _ _ _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc β i).trans hβ)]
  change _root_.SerrePositivity.DifferentialGraded.representable R (s.val.obj i.castSucc).left = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s i]

lemma dgGluingNativePinchedPrism_source_one (β : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hβ : β i = 1) :
    (dgGluingNativePinchedPrismSimplex R C D M s β).obj i.castSucc = M.rightAt X.right := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R D (RightModule R C) M.toFunctor
    (s.val.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)).toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)).obj
    i.castSucc = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_one R D (RightModule R C) M.toFunctor _ _ _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc β i).trans hβ)]
  change M.rightAt (s.val.obj i.castSucc).right = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s i]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
