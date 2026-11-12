module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictAugmentationHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyBarCokernel
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-!
概要：filtered poset 上の strict 図式の正規化 bar 標準射は擬同型である。
方針：coherent C1 の余核と標的ホモロジー余錐の余核を、同じ標準射で比較する。
規約：正則 κ や native 普遍性を追加仮定せず、任意の filtered poset で示す。
使われ方：D-bar B の native 普遍性と組み合わせる strict/native 比較 C2。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

lemma dgCoherentBarStrictColimitAugmentation_homologyIsIso (x : D) (p : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation R D F)) (p + 1)) := by
  let G := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F
  let H := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (p + 1)
  let h₁ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarIsCokernel R D G x p
  let h₂ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegAugmentationIsCokernel R H
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyCocone R D F x (p + 1))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyCoconeIsColimit R D F x (p + 1))
  let e := h₁.coconePointUniqueUpToIso h₂
  letI : Epi (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation R D G x (p + 1)) :=
    epi_of_isColimit_cofork h₁
  have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation R D G x (p + 1) ≫ e.hom =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegAugmentation R H
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyCocone R D F x (p + 1)) :=
    h₁.comp_coconePointUniqueUpToIso_hom h₂ WalkingParallelPair.one
  have hf : HomologicalComplex.homologyMap
      ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation R D F)) (p + 1) =
        e.hom := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation R D G x (p + 1))).mp
    exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentation_homology R D F x (p + 1)).trans he.symm
  rw [hf]
  infer_instance

lemma dgCoherentBarStrictColimitAugmentation_homologyIsIsoAt
    (x : D) (p q : ℤ) (hpq : p + 1 = q) :
    IsIso (HomologicalComplex.homologyMap
      ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation R D F)) q) := by
  subst q
  exact dgCoherentBarStrictColimitAugmentation_homologyIsIso R D F x p

lemma dgCoherentBarStrictColimitAugmentation_quasiIso :
    moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation R D F) := by
  intro x
  apply (_root_.quasiIso_iff _).mpr
  intro q
  apply (_root_.quasiIsoAt_iff_isIso_homologyMap _ _).mpr
  exact dgCoherentBarStrictColimitAugmentation_homologyIsIsoAt R D F x (q - 1) q (by omega)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
