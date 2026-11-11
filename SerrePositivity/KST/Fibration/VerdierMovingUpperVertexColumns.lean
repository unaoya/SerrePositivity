module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperShortFaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingFaceEndpoints

/-!
概要：動く実上側族の三頂点の全区間列を、同じ元の定値対象へ厳密回収する。
方針：二短辺の全族回収を固定両端付き区間 Hom の端点制限へ渡す。
規約：第二短辺自体は動いたまま保持する。
使われ方：K-6 c4 の全四角柱の上側縦辺の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌)

/-- 概要：同じ上側全族の始点列は元の実核の core Kan 対象に定値。
方針：元の第一短辺を区間 Hom の始点面へ制限する。
規約：全パラメータの厳密等式。使われ方：始点縦辺の回収。 -/
theorem verdierMovingUpperFamily_source_column :
    ((stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ▷
      (Δ[1] : SSet.{u + 1})) ≫ verdierMovingUpperFamily d ℓ =
    fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))) := by
  rw [comp_whiskerRight, Category.assoc, verdierMovingUpperFamily_first,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_source]
  rfl

/-- 概要：同じ上側全族の中点列は元の実核の全 S• Kan 対象に定値。
方針：元の第一短辺を区間 Hom の終点面へ制限する。
規約：元の全 S• 中間対象を保持。使われ方：中点縦辺の回収。 -/
theorem verdierMovingUpperFamily_middle_column :
    ((stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ▷
      (Δ[1] : SSet.{u + 1})) ≫ verdierMovingUpperFamily d ℓ =
    fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (fullSRealizationKanObject d.left)) := by
  rw [comp_whiskerRight, Category.assoc, verdierMovingUpperFamily_first,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_target]
  rfl

/-- 概要：動く第二短辺の終点列は元の実商の core Kan 対象に定値。
方針：同じ第二短辺全族を固定終点面へ制限する。
規約：第二短辺を定値族へ置き換えない。使われ方：終点縦辺の回収。 -/
theorem verdierMovingUpperFamily_target_column :
    ((stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ▷
      (Δ[1] : SSet.{u + 1})) ≫ verdierMovingUpperFamily d ℓ =
    fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))) := by
  rw [comp_whiskerRight, Category.assoc, verdierMovingUpperFamily_last,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_target]
  rfl

end SerrePositivity.KST.Fibration
