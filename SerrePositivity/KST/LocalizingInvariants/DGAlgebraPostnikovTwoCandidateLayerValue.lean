module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoOriginalLayerMaps
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCandidateRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofHomology

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCandidateLayerValue

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
      (d.targetCoefficientHomologyIso R).hom :=
  PostnikovSuccessorClassInverseData.classModelCandidateRoof_homology_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceUpperRoof_homology_layer :
    (d.sourceUpperRoof R).homologyValue R (-2) ≫ (d.sourceLayerIso R).hom =
      (postnikovUpperClassLayerHomologyIso R
        (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom ≫
        (d.sourceCoefficientHomologyIso R).inv :=
  PostnikovSuccessorClassInverseData.sourceUpperRoof_homology_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetUpperRoof_homology_layer :
    (targetUpperRoof (A := A) (j := j) R).homologyValue R (-2) ≫
      (postnikovUpperClassLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
        (postnikovClassModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom :=
  PostnikovSuccessorClassInverseData.targetUpperRoof_homology_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (j := j)

/-- 元の τ₂ 代数間の実候補 roof の作用は、同じ係数逆 Γ の作用に等しい。 -/
lemma candidateRoof_homology_layer :
    (d.candidateRoof R).homologyValue R (-2) ≫
      (postnikovUpperClassLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
    (postnikovUpperClassLayerHomologyIso R
        (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom ≫
      (d.sourceCoefficientHomologyIso R).inv ≫
      homologyMap (d.classCoefficient R).hom (-3) ≫
      (d.targetCoefficientHomologyIso R).hom :=
  PostnikovSuccessorClassInverseData.candidateRoof_homology_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
