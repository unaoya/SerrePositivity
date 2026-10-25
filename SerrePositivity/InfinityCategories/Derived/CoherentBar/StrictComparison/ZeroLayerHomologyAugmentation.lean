module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroLayerInclusion
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyBarCofork

/-!
概要：零次元層の実包含は C1 のホモロジー増大を与える。
方針：同じ零段階同型を前合成し、実段階包含の比較を使う。
規約：指定増大射との後合成を後から行える等式として公開する。
使われ方：native 増大の全零次元係数による擬同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ dgNerve R (RightModule R D))

lemma dgBarZeroLayerInclusion_homology (x : D) (q : ℤ) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (dgBarZeroLayerInclusion R D G)) q =
        (dgCoherentBarNaturalLayerHomologyIso R D G x 0 q q (by omega)).hom ≫
          dgCoherentBarHomologyBarAugmentation R D G x q := by
  rw [← cancel_epi (HomologicalComplex.homologyMapIso (dgCoherentBarZeroStageIso R D G x) q).hom]
  change HomologicalComplex.homologyMap (dgCoherentBarZeroStageIso R D G x).hom q ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp, dgBarZeroStage_inclusion]
  dsimp only [dgCoherentBarHomologyBarAugmentation, dgCoherentBarZeroStageHomologyIso,
    Iso.trans_inv, HomologicalComplex.homologyMapIso_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories
