module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Edge
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftPostcomposition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.EdgeCoefficients
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ ModuleCategory R D) (c : Cocone F)

set_option maxHeartbeats 200000 in
-- The face coefficient carries an endpoint transport in the selected enriched Hom end.
lemma dgCoherentBarStrictAugmentation_postFace_edge (s : (nerve J) _⦋1⦌) :
    (eHomWhiskerLeft (Complex R)
      (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
      (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (dgCoherentBarFaceColumn R D (dgCoherentBarStrictDiagram R D F) (n := 0) s 0) =
      (eHomWhiskerLeft (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
        (c.ι.app (s.obj 0))).f 1
          (moduleShiftOutElement R D 1 (ForgetEnrichment.to (Complex R)
            (F.obj (s.obj 0)))) := by
  unfold dgCoherentBarFaceColumn
  rw [dgCoherentBarStrictAugmentation_postInclusion R D F c]
  have h := dgStrictPostcompose_eq_of_heq R D
    (T := dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
    (N := dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)
      (dgCoherentBarFace (n := 0) s (0 : Fin 1).succ))
    (N' := ForgetEnrichment.of (Complex R)
      (shiftModule 0 (ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))))
    (P := c.pt)
    rfl
    (dgCoherentBarStrictAugmentationRawColumn R D F c (dgCoherentBarFace (n := 0) s (0 : Fin 1).succ))
    ((moduleShiftZeroIsoObj R D
      (ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))).hom ≫ c.ι.app (s.obj 0))
    (dgStrictEdgeFaceAugmentation R D F c s) 1
    (dgCoherentBarFaceBlock R D (dgCoherentBarStrictDiagram R D F) (n := 0) s 0)
    (moduleHomShiftBlock R D 1 0
      (M := ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))
      (N := ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))
      (q := 0) (k := 1) (unitElement (D := RightModule R D) R (ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))).val
        (show (1 : ℤ) + 0 - 0 = 1 by omega))
    (dgStrictEdgeFaceBlock R D F s)
  convert! h using 1
  exact (dgStrictPostcompose_shiftBlock_unit R D
    (M := F.obj (s.obj 0)) (P := c.pt) (c.ι.app (s.obj 0))).symm

lemma dgCoherentBarStrictAugmentation_postPrefix_edge (s : (nerve J) _⦋1⦌) :
    (eHomWhiskerLeft (Complex R)
      (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
      (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (dgCoherentBarPrefixColumn R D (dgCoherentBarStrictDiagram R D F) s 0 (by decide)) =
      (eHomWhiskerLeft (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
        (c.ι.app (s.obj 0))).f 1
          (moduleShiftOutElement R D 1 (ForgetEnrichment.to (Complex R)
            (F.obj (s.obj 0)))) := by
  unfold dgCoherentBarPrefixColumn
  refine Eq.trans (dgCoherentBarStrictAugmentation_postInclusion R D F c
    (M := dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
    (dgCoherentBarTail s 1 (by decide)) 1
    (dgCoherentBarPrefixBlock R D (dgCoherentBarStrictDiagram R D F) s 0 (by decide))) ?_
  refine Eq.trans (dgStrictPostcompose_eq_of_heq R D
    (T := dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨1, s⟩)
    (N' := ForgetEnrichment.of (Complex R)
      (shiftModule 0 (ForgetEnrichment.to (Complex R) (F.obj (s.obj 1))))) rfl
    (dgCoherentBarStrictAugmentationRawColumn R D F c (dgCoherentBarTail s 1 (by decide)))
    ((moduleShiftZeroIsoObj R D
      (ForgetEnrichment.to (Complex R) (F.obj (s.obj 1)))).hom ≫ c.ι.app (s.obj 1))
    (dgStrictEdgeTailAugmentation R D F c s) 1
    (dgCoherentBarPrefixBlock R D (dgCoherentBarStrictDiagram R D F) s 0 (by decide))
    (moduleHomShiftBlock R D 1 0
      (closedHomEquiv R (RightModule R D) (F.obj (s.obj 0)) (F.obj (s.obj 1))
        (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))))).val
        (show (1 : ℤ) + 0 - 0 = 1 by omega))
    (dgStrictEdgePrefixBlock R D F s)) ?_
  have h := dgStrictPostcompose_shiftBlock_closed R D
    (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)))) (c.ι.app (s.obj 1))
  rw [c.w] at h
  exact h

end SerrePositivity.InfinityCategories
