module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraBoundedMapValuePro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverTowers

/-!
概要：connective な実代数の塔にも、共通下界による有限範囲の pro 判定を拡張する。
方針：非正次数 cover で既存判定を適用し、元の準同型 counit 正方形で反映する。
規約：元の塔を非正次数と仮定しない。使われ方：実像因子分解の標的側の値の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R]

lemma connectiveCover_isGE_of_isConnective (A : Mon (Complex R)) (hA : IsConnective R A)
    (bound : ℤ) (hb : A.X.IsGE bound) : (connectiveCover R A).X.IsGE bound := by
  have := connectiveCoverInclusion_quasiIso R A hA
  apply (CochainComplex.isGE_iff _ _).2
  intro j hj
  exact (exactAt_iff_of_quasiIsoAt (connectiveCoverInclusion R A).hom j).2
    (CochainComplex.exactAt_of_isGE A.X bound j hj)

lemma coverTowerCounit_square {X Y : Tower (Mon (Complex R))} (f : LevelHom X Y) :
    (f.map (connectiveCoverFunctor R)).comp (coverTowerCounit R Y) =
      (coverTowerCounit R X).comp f := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact (connectiveCoverCounit R).naturality (f.app i)

variable {X Y : Tower (Mon (Complex R))} (f : LevelHom X Y)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma algebraMap_isProIso_of_bounded_connective (hL : InvertsConnectiveQuasiIsos R L)
    (cutoff : ℤ) (hc : 0 ≤ cutoff)
    (hX : ∀ i, IsConnective R (X.obj i)) (hY : ∀ i, IsConnective R (Y.obj i))
    (hA : ∀ i, (X.obj i).X.IsGE (-cutoff)) (hB : ∀ i, (Y.obj i).X.IsGE (-cutoff))
    (h : ∀ j : ℤ, 0 ≤ j → j ≤ cutoff → IsProIso (f.map (groups R j))) :
    IsProIso (f.map L) := by
  let fc := f.map (connectiveCoverNonpositive R)
  have groupCover (j : ℤ) (hj : 0 ≤ j) (hjn : j ≤ cutoff) :
      IsProIso ((fc.map (nonpositiveInclusion R)).map (groups R j)) := by
    have : ∀ i, IsIso (((coverTowerCounit R X).map (groups R j)).app i) := fun i =>
      groups_map_isIso_of_quasiIso R _ (connectiveCoverInclusion_quasiIso R _ (hX i)) j
    have : ∀ i, IsIso (((coverTowerCounit R Y).map (groups R j)).app i) := fun i =>
      groups_map_isIso_of_quasiIso R _ (connectiveCoverInclusion_quasiIso R _ (hY i)) j
    apply TowerDiagram.proIso_of_square_reverse
      ((fc.map (nonpositiveInclusion R)).map (groups R j)) (f.map (groups R j))
      ((coverTowerCounit R X).map (groups R j)) ((coverTowerCounit R Y).map (groups R j))
    · rw [← TowerDiagram.levelHom_map_comp, ← TowerDiagram.levelHom_map_comp]
      exact congrArg (fun t => t.map (groups R j)) (coverTowerCounit_square R f)
    · exact h j hj hjn
  have coverPro := nonpositiveMap_isProIso_of_bounded_connective R fc L hL cutoff hc
    (fun i => connectiveCover_isGE_of_isConnective R _ (hX i) _ (hA i))
    (fun i => connectiveCover_isGE_of_isConnective R _ (hY i) _ (hB i)) groupCover
  have : ∀ i, IsIso (((coverTowerCounit R X).map L).app i) := fun i =>
    hL (connectiveCover_isConnective R _) (hX i) _
      (connectiveCoverInclusion_quasiIso R _ (hX i))
  have : ∀ i, IsIso (((coverTowerCounit R Y).map L).app i) := fun i =>
    hL (connectiveCover_isConnective R _) (hY i) _
      (connectiveCoverInclusion_quasiIso R _ (hY i))
  apply TowerDiagram.proIso_of_square ((fc.map (nonpositiveInclusion R)).map L) (f.map L)
    ((coverTowerCounit R X).map L) ((coverTowerCounit R Y).map L)
  · rw [← TowerDiagram.levelHom_map_comp, ← TowerDiagram.levelHom_map_comp]
    exact congrArg (fun t => t.map L) (coverTowerCounit_square R f)
  · exact coverPro

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
