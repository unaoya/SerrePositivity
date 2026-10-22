module
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphBimoduleIso
public import SerrePositivity.DifferentialGraded.Tensor.OuterUnitRestriction
public import SerrePositivity.InfinityCategories.Derived.DGDiagonalBimoduleUnit
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelAugmentation
public import SerrePositivity.DifferentialGraded.Tensor.RightUnitRestriction
/-!
概要：graph と対角の実比較を左右の閉零単位子へ同定する。
方針：対角の二単位子の一致と既存の外側制限・中間制限の単位正方形を使う。
規約：quasi-equivalence は仮定しない。使われ方：cell diagonal の単位比較。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R C D)
omit [Small.{u} C] in
lemma dgKernelSourceGraphBimoduleIso_diagonal :
    dgKernelSourceGraphBimoduleIso R C D D F (Bimodule.diagonal R D) =
      BimoduleTensor.leftBimoduleUnitIso R D C (functorGraph R C D F) := by
  change BimoduleTensor.composeLeftRestrictionIso R D D D C F
      (BimoduleCategory.of R D D (Bimodule.diagonal R D))
      (BimoduleCategory.of R D D (Bimodule.diagonal R D)) ≪≫
    (BimoduleCategory.middleLeftRestrictionFunctor R D D C F).mapIso
      (BimoduleTensor.rightBimoduleUnitIso R D D (Bimodule.diagonal R D)) = _
  rw [dgDiagonalBimoduleUnitIso_eq]
  apply Iso.ext
  exact BimoduleTensor.leftBimoduleUnitIso_leftRestriction R D D C F
    (BimoduleCategory.of R D D (Bimodule.diagonal R D))
lemma dgKernelTargetModelAugmentation_diagonal :
    dgKernelTargetModelAugmentation R C C D F
      (BimoduleCategory.of R D C (F.comp (Bimodule.diagonal R D)))
      (BimoduleCategory.of R C C (Bimodule.diagonal R C))
      (Bimodule.diagonalRestrictionMap R C D F) =
        (BimoduleTensor.rightBimoduleUnitIso R D C (functorGraph R C D F)).hom := by
  change BimoduleTensor.composeMap R D C C
      (𝟙 (BimoduleCategory.of R D C (functorGraph R C D F)))
      (Bimodule.diagonalRestrictionMap R C D F) ≫
    BimoduleTensor.middleRestrictionComparisonMap R D D C C F
      (Bimodule.diagonal R D) (F.comp (Bimodule.diagonal R D)) ≫
    (BimoduleTensor.leftBimoduleUnitIso R D C (functorGraph R C D F)).hom = _
  rw [← dgKernelSourceGraphBimoduleIso_diagonal]
  change BimoduleTensor.composeMap R D C C
      (𝟙 (BimoduleCategory.of R D C (functorGraph R C D F)))
      (Bimodule.diagonalRestrictionMap R C D F) ≫
    BimoduleTensor.middleRestrictionComparisonMap R D D C C F
      (Bimodule.diagonal R D) (F.comp (Bimodule.diagonal R D)) ≫
    (BimoduleTensor.composeLeftRestrictionIso R D D D C F
      (BimoduleCategory.of R D D (Bimodule.diagonal R D))
      (BimoduleCategory.of R D D (Bimodule.diagonal R D))).hom ≫
    (BimoduleCategory.middleLeftRestrictionFunctor R D D C F).map
      (BimoduleTensor.rightBimoduleUnitIso R D D (Bimodule.diagonal R D)).hom = _
  exact BimoduleTensor.rightUnitRestriction R D D C F
    (BimoduleCategory.of R D D (Bimodule.diagonal R D))
end
end SerrePositivity.InfinityCategories
