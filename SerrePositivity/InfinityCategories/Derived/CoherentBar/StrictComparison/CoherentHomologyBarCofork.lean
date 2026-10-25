module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageIso
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyCokernel
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyComparison

/-!
概要：非退化 H(G) bar の零次から実 bar のホモロジーへの標準余核射。
方針：零段階・零次元層・係数ホモロジーの自然な同型を合わせる。
規約：実連結射と交代面微分の比較を使う。
使われ方：実 bar のホモロジーと colim H(G) の標準同型。
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
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

def dgCoherentBarZeroStageHomologyIso (x : D) (q : ℤ) :
    (dgCoherentBarNormalizedStageComplex R D G x 0).homology q ≅
      (dgHomologyBarNondegComplex R (dgCoherentBarHomologyDiagram R D G x q)).X 0 :=
  HomologicalComplex.homologyMapIso (dgCoherentBarZeroStageIso R D G x) q ≪≫
    dgCoherentBarNaturalLayerHomologyIso R D G x 0 q q (by omega)

def dgCoherentBarHomologyBarAugmentation (x : D) (q : ℤ) :
    (dgHomologyBarNondegComplex R (dgCoherentBarHomologyDiagram R D G x q)).X 0 ⟶
      ((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology q :=
  (dgCoherentBarZeroStageHomologyIso R D G x q).inv ≫
    HomologicalComplex.homologyMap (dgCoherentBarNormalizedStageInclusion R D G x 0) q

lemma dgCoherentBarFirstConnecting_homologyBar (x : D) (p : ℤ) :
    (dgCoherentBarLayerSequence_shortExact R D G x 0).δ p (p + 1) (by simp) ≫
      (dgCoherentBarZeroStageHomologyIso R D G x (p + 1)).hom =
    (dgCoherentBarNaturalLayerHomologyIso R D G x 1 p (p + 1) (by omega)).hom ≫
      (dgHomologyBarNondegComplex R (dgCoherentBarHomologyDiagram R D G x (p + 1))).d 1 0 := by
  change (dgCoherentBarLayerSequence_shortExact R D G x 0).δ p (p + 1) (by simp) ≫
    (HomologicalComplex.homologyMap (dgCoherentBarStageToLayer R D G x 0) (p + 1) ≫
      (dgCoherentBarNaturalLayerHomologyIso R D G x 0 (p + 1) (p + 1) (by omega)).hom) = _
  rw [← Category.assoc]
  exact dgCoherentBarConnectingHomology_comparison R D G x 0 p (p + 1) (p + 1)
    rfl (by omega) (by omega)

lemma dgCoherentBarHomologyBarAugmentation_d_one (x : D) (p : ℤ) :
    (dgHomologyBarNondegComplex R (dgCoherentBarHomologyDiagram R D G x (p + 1))).d 1 0 ≫
      dgCoherentBarHomologyBarAugmentation R D G x (p + 1) = 0 := by
  rw [← cancel_epi
    (dgCoherentBarNaturalLayerHomologyIso R D G x 1 p (p + 1) (by omega)).hom]
  rw [← Category.assoc, ← dgCoherentBarFirstConnecting_homologyBar]
  dsimp only [dgCoherentBarHomologyBarAugmentation]
  rw [Category.assoc, Iso.hom_inv_id_assoc,
    dgCoherentBarFirstConnecting_inclusion_zero, comp_zero]

end SerrePositivity.InfinityCategories
