module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationColumns
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Edge
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftPostcomposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.EdgeCoefficients
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：strict augmentation の一次元の面と prefix は余錐の可換式で一致する。
方針：零 shift を消去し、元の図式の閉零射と余錐の脚の合成に戻す。
規約：元の加群射の全 dg 自然性を保つ。
使われ方：標準 augmentation と bar 微分の可換性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (c : Cocone F)

set_option maxHeartbeats 200000 in
-- The face coefficient carries an endpoint transport in the selected enriched Hom end.
lemma dgCoherentBarStrictAugmentation_postFace_edge (s : (nerve J) _⦋1⦌) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) (n := 0) s 0) =
      (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
        (c.ι.app (s.obj 0))).f 1
          (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
            (F.obj (s.obj 0)))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentation_postInclusion R D F c]
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictPostcompose_eq_of_heq R D
    (T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
    (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace (n := 0) s (0 : Fin 1).succ))
    (N' := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.DifferentialGraded.shiftModule 0 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))))
    (P := c.pt)
    rfl
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawColumn R D F c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace (n := 0) s (0 : Fin 1).succ))
    ((_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))).hom ≫ c.ι.app (s.obj 0))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictEdgeFaceAugmentation R D F c s) 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) (n := 0) s 0)
    (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D 1 0
      (M := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))
      (N := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))
      (q := 0) (k := 1) (_root_.SerrePositivity.DifferentialGraded.unitElement (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D) R (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))).val
        (show (1 : ℤ) + 0 - 0 = 1 by omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictEdgeFaceBlock R D F s)
  convert! h using 1
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictPostcompose_shiftBlock_unit R D
    (M := F.obj (s.obj 0)) (P := c.pt) (c.ι.app (s.obj 0))).symm

lemma dgCoherentBarStrictAugmentation_postPrefix_edge (s : (nerve J) _⦋1⦌) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s 0 (by decide)) =
      (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
        (c.ι.app (s.obj 0))).f 1
          (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D 1 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
            (F.obj (s.obj 0)))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn
  refine Eq.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentation_postInclusion R D F c
    (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by decide)) 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s 0 (by decide))) ?_
  refine Eq.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictPostcompose_eq_of_heq R D
    (T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
    (N' := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.DifferentialGraded.shiftModule 0 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 1))))) rfl
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawColumn R D F c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by decide)))
    ((_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 1)))).hom ≫ c.ι.app (s.obj 1))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictEdgeTailAugmentation R D F c s) 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s 0 (by decide))
    (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D 1 0
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (F.obj (s.obj 0)) (F.obj (s.obj 1))
        (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))))).val
        (show (1 : ℤ) + 0 - 0 = 1 by omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictEdgePrefixBlock R D F s)) ?_
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictPostcompose_shiftBlock_closed R D
    (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)))) (c.ι.app (s.obj 1))
  rw [c.w] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
