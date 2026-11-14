module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationGraded
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.EdgeObjects
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Edge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Faces.DGCoherentBarFaceDifferential

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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (c : Cocone F)

lemma dgStrictEdgeFaceFamily (s : (nerve J) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace (n := 0) s (0 : Fin 1).succ) =
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.DifferentialGraded.shiftModule 0 (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))) := rfl

lemma dgStrictEdgeFaceAugmentation (s : (nerve J) _⦋1⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawColumn R D F c
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace (n := 0) s (0 : Fin 1).succ))
      ((_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))).hom ≫ c.ι.app (s.obj 0)) :=
  HEq.rfl

lemma dgStrictEdgeFaceBlock (s : (nerve J) _⦋1⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) (n := 0) s 0)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D 1 0
        (M := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))
        (N := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))
        (q := 0) (k := 1) (_root_.SerrePositivity.DifferentialGraded.unitElement (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D) R (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)))).val
        (show (1 : ℤ) + 0 - 0 = 1 by omega)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock_heq R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) (n := 0) s 0

lemma dgStrictEdgeTailAugmentation (s : (nerve J) _⦋1⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawColumn R D F c
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by decide)))
      ((_root_.SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj R D
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 1)))).hom ≫ c.ι.app (s.obj 1)) :=
  HEq.rfl

lemma dgStrictEdgePrefixBlock (s : (nerve J) _⦋1⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s 0 (by decide))
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D 1 0
        (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (F.obj (s.obj 0)) (F.obj (s.obj 1))
          (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))))).val
        (show (1 : ℤ) + 0 - 0 = 1 by omega)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictPrefixHom_edge R D F]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
