module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelSourceGraphBimoduleIso
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Restriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGDiagonalBimoduleUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelAugmentation
public import SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction
/-!
概要：graph と対角の実比較を左右の閉零単位子へ同定する。
方針：対角の二単位子の一致と既存の外側制限・中間制限の単位正方形を使う。
規約：quasi-equivalence は仮定しない。使われ方：cell diagonal の単位比較。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (C D : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D)
omit [Small.{u} C] in
lemma dgKernelSourceGraphBimoduleIso_diagonal :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelSourceGraphBimoduleIso R C D D F (Bimodule.diagonal R D) =
      _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F) := by
  change _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeLeftRestrictionIso R D D D C F
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D))
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)) ≪≫
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R D D C F).mapIso
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDiagonalBimoduleUnitIso_eq]
  apply Iso.ext
  exact _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso_leftRestriction R D D C F
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D))
lemma dgKernelTargetModelAugmentation_diagonal :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation R C C D F
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D C (F.comp (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)))
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R C C (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R C))
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonalRestrictionMap R C D F) =
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R D C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F)).hom := by
  change _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R D C C
      (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F)))
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonalRestrictionMap R C D F) ≫
    _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.middleRestrictionComparisonMap R D D C C F
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D) (F.comp (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)) ≫
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F)).hom = _
  rw [← dgKernelSourceGraphBimoduleIso_diagonal]
  change _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R D C C
      (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F)))
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonalRestrictionMap R C D F) ≫
    _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.middleRestrictionComparisonMap R D D C C F
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D) (F.comp (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)) ≫
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeLeftRestrictionIso R D D D C F
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D))
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D))).hom ≫
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R D D C F).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)).hom = _
  exact _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitRestriction R D D C F
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D))
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
