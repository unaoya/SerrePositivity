module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationGraded
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.EdgeObjects
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Edge
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarFaceDifferential

/-!
概要：辺の面の係数と augmentation の脚の端点を明示する。
方針：元の shift ブロックの異種等号を保ち、strict nerve の頂点を計算する。
規約：端点輸送を消去したと仮定しない。
使われ方：strict augmentation の一次元係数の相殺。
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

lemma dgStrictEdgeFaceFamily (s : (nerve J) _⦋1⦌) :
    dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)
      (dgCoherentBarFace (n := 0) s (0 : Fin 1).succ) =
    ForgetEnrichment.of (Complex R)
      (shiftModule 0 (ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))) := rfl

lemma dgStrictEdgeFaceAugmentation (s : (nerve J) _⦋1⦌) :
    HEq (dgCoherentBarStrictAugmentationRawColumn R D F c
      (dgCoherentBarFace (n := 0) s (0 : Fin 1).succ))
      ((moduleShiftZeroIsoObj R D
        (ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))).hom ≫ c.ι.app (s.obj 0)) :=
  HEq.rfl

lemma dgStrictEdgeFaceBlock (s : (nerve J) _⦋1⦌) :
    HEq (dgCoherentBarFaceBlock R D (dgCoherentBarStrictDiagram R D F) (n := 0) s 0)
      (moduleHomShiftBlock R D 1 0
        (M := ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))
        (N := ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))
        (q := 0) (k := 1) (unitElement (D := RightModule R D) R (ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))).val
        (show (1 : ℤ) + 0 - 0 = 1 by omega)) := by
  exact dgCoherentBarFaceBlock_heq R D (dgCoherentBarStrictDiagram R D F) (n := 0) s 0

lemma dgStrictEdgeTailAugmentation (s : (nerve J) _⦋1⦌) :
    HEq (dgCoherentBarStrictAugmentationRawColumn R D F c
      (dgCoherentBarTail s 1 (by decide)))
      ((moduleShiftZeroIsoObj R D
        (ForgetEnrichment.to (Complex R) (F.obj (s.obj 1)))).hom ≫ c.ι.app (s.obj 1)) :=
  HEq.rfl

lemma dgStrictEdgePrefixBlock (s : (nerve J) _⦋1⦌) :
    HEq (dgCoherentBarPrefixBlock R D (dgCoherentBarStrictDiagram R D F) s 0 (by decide))
      (moduleHomShiftBlock R D 1 0
        (closedHomEquiv R (RightModule R D) (F.obj (s.obj 0)) (F.obj (s.obj 1))
          (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))))).val
        (show (1 : ℤ) + 0 - 0 = 1 by omega)) := by
  unfold dgCoherentBarPrefixBlock
  rw [dgCoherentBarStrictPrefixHom_edge R D F]
  rfl

end SerrePositivity.InfinityCategories
