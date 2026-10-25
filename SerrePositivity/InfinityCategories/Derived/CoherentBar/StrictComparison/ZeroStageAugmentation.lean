module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationComponents
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageIso

/-!
概要：零段階上の strict 増大は零次元層の graded 増大と一致する。
方針：零次元支持上で層射影と層包含が互いに逆であることを使う。
規約：実 bar の閉じた増大と元の dg 加群作用を保持する。
使われ方：標準余核射と strict 余極限の全ての脚の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ ModuleCategory R D) (c : Cocone F)

lemma dgCoherentBarZeroStage_augmentation (x : D) :
    (dgCoherentBarZeroStageIso R D (dgCoherentBarStrictDiagram R D F) x).hom ≫
      (moduleEvaluation R D x).map
        (dgCoherentBarLayerInclusion R D (dgCoherentBarStrictDiagram R D F) 0 ≫
          dgCoherentBarStrictAugmentationGraded R D F c) =
    dgCoherentBarNormalizedStageInclusion R D (dgCoherentBarStrictDiagram R D F) x 0 ≫
      (moduleEvaluation R D x).map (dgCoherentBarStrictAugmentation R D F c) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    CategoryTheory.Functor.map_comp, dgCoherentBarStrictAugmentation_f]
  change ((moduleEvaluation R D x).map (dgCoherentBarStrictAugmentationGraded R D F c)).f q
    ((moduleDegreeEvaluation R D x q).map
      (dgCoherentBarLayerInclusion R D (dgCoherentBarStrictDiagram R D F) 0)
      ((moduleDegreeEvaluation R D x q).map
        (dgCoherentBarLayerProjection R D (dgCoherentBarStrictDiagram R D F) 0) z.val)) =
    ((moduleEvaluation R D x).map (dgCoherentBarStrictAugmentationGraded R D F c)).f q z.val
  rw [dgCoherentBarZeroLayer_recover R D (dgCoherentBarStrictDiagram R D F) x q z.val z.property]

end SerrePositivity.InfinityCategories
