module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoOriginalLayerMaps
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCandidateRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofHomology

/-!
概要：二切断候補 roof の全 zigzag の H⁻² 作用を、構成済みの実係数射に同定する。
方針：逆準同型の作用は実逆三角形で消去し、四模型射と元の両端比較の式を合成する。
規約：ホモロジーの式から代数射の逆三角形を推論しない。使われ方：実候補の π₂ 検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma classModelCandidateRoof_homology_layer :
    (d.classModelCandidateRoof R).homologyValue R (-2) ≫
      (postnikovClassModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
    (d.sourceLayerIso R).hom ≫ homologyMap (d.classCoefficient R).hom (-3) ≫
      (d.targetCoefficientHomologyIso R).hom := by
  have hinv : (SurjectiveRoof.ofQuasiIsoInverse R (d.targetToPath R)
      (d.targetToPath_quasiIso R)).homologyValue R (-2) ≫
        (d.targetComposedLayerIso R).hom = (d.pathLayerIso R).hom := by
    have := d.targetToPath_quasiIso R
    apply (cancel_epi (homologyMap (d.targetToPath R).hom (-2))).1
    rw [← Category.assoc, SurjectiveRoof.comp_inverse_homologyValue, Category.id_comp,
      d.targetToPath_layer R]
  rw [classModelCandidateRoof, SurjectiveRoof.postcompose_homologyValue,
    SurjectiveRoof.comp_homologyValue, SurjectiveRoof.ofHom_homologyValue,
    Mon.comp_hom', homologyMap_comp, Mon.comp_hom', homologyMap_comp]
  simp only [Category.assoc]
  rw [d.targetToOriginalModel_layer R, ← Category.assoc _ (d.targetLayerIso R).hom,
    d.targetToStandard_layer R, ← Category.assoc _ (d.targetComposedLayerIso R).hom,
    hinv, ← Category.assoc _ (d.pathLayerIso R).hom, d.imageToPath_layer R,
    ← Category.assoc _ (d.imageLayerIso R).hom, d.sourceToImage_layer R]
  simp only [Category.assoc]

lemma sourceUpperRoof_homology_layer :
    (d.sourceUpperRoof R).homologyValue R (-2) ≫ (d.sourceLayerIso R).hom =
      (postnikovUpperClassLayerHomologyIso R
        (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom ≫
        (d.sourceCoefficientHomologyIso R).inv := by
  apply (cancel_mono (d.sourceCoefficientHomologyIso R).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← d.sourceToOriginalModel_layer R, sourceUpperRoof, SurjectiveRoof.comp_homologyValue,
    SurjectiveRoof.ofHom_homologyValue]
  simp only [Category.assoc]
  rw [← Category.assoc _ (homologyMap (d.sourceToOriginalModel R).hom (-2)),
    SurjectiveRoof.inverse_homologyValue_comp, Category.id_comp]
  rfl

lemma targetUpperRoof_homology_layer :
    (targetUpperRoof (A := A) (j := j) R).homologyValue R (-2) ≫
      (postnikovUpperClassLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
        (postnikovClassModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom := by
  change (SurjectiveRoof.ofQuasiIsoInverse R _ _).homologyValue R (-2) ≫
    (homologyMap (postnikovHomotopyPullbackComparison R (A.obj j).obj 1 (by omega)).hom (-2) ≫
      (postnikovClassModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom) = _
  rw [← Category.assoc, SurjectiveRoof.inverse_homologyValue_comp, Category.id_comp]

/-- 元の τ₂ 代数間の実候補 roof の作用は、同じ係数逆 Γ の作用に等しい。 -/
lemma candidateRoof_homology_layer :
    (d.candidateRoof R).homologyValue R (-2) ≫
      (postnikovUpperClassLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
    (postnikovUpperClassLayerHomologyIso R
        (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom ≫
      (d.sourceCoefficientHomologyIso R).inv ≫
      homologyMap (d.classCoefficient R).hom (-3) ≫
      (d.targetCoefficientHomologyIso R).hom := by
  rw [candidateRoof, SurjectiveRoof.nonpositiveNormalization_homologyValue, rawCandidateRoof,
    SurjectiveRoof.comp_homologyValue, SurjectiveRoof.comp_homologyValue]
  simp only [Category.assoc]
  rw [targetUpperRoof_homology_layer R, d.classModelCandidateRoof_homology_layer R,
    ← Category.assoc _ (d.sourceLayerIso R).hom, d.sourceUpperRoof_homology_layer R,
    Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
