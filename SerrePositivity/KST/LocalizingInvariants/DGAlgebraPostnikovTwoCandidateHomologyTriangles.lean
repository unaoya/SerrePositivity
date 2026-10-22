module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCoefficientTriangles
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCandidateLayerValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationLayers

/-!
概要：元の τ₂ 代数射と実候補 roof の H⁻² 作用が、両順序で元の遷移と一致する。
方針：同じ係数 Γ の両三角形を、元の上段層同型の自然性を介して移す。
規約：ホモロジーの両三角形であり、実代数射の両逆をまだ主張しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma candidateRoof_homology_action :
    (d.candidateRoof R).homologyValue R (-2) ≫
      (postnikovUpperClassLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
    (postnikovUpperClassLayerHomologyIso R
      (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom ≫ d.coefficientHomologyAction R := by
  simpa only [coefficientHomologyAction, Category.assoc] using d.candidateRoof_homology_layer R

lemma candidateRoof_homology_left :
    homologyMap (postnikovMap R (f.app d.layerInverse.zero.stage).hom 2).hom (-2) ≫
      (d.candidateRoof R).homologyValue R (-2) = homologyMap (postnikovMap R
      (A.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom 2).hom (-2) := by
  let h := d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
  have hf := postnikovUpperClassLayerHomologyIso_naturality R
    (f.app d.layerInverse.zero.stage).hom 1 (by omega)
  have ht := postnikovUpperClassLayerHomologyIso_naturality R (A.transition h).hom 1 (by omega)
  simp only [Int.reduceAdd, Int.reduceNeg] at hf ht
  apply (cancel_mono (postnikovUpperClassLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom).1
  rw [Category.assoc, d.candidateRoof_homology_action R, ← Category.assoc, hf, Category.assoc,
    d.coefficientHomologyAction_left R]
  exact ht.symm

lemma candidateRoof_homology_right : (d.candidateRoof R).homologyValue R (-2) ≫
    homologyMap (postnikovMap R (f.app j).hom 2).hom (-2) = homologyMap (postnikovMap R
      (B.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom 2).hom (-2) := by
  let h := d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
  have hf := postnikovUpperClassLayerHomologyIso_naturality R (f.app j).hom 1 (by omega)
  have ht := postnikovUpperClassLayerHomologyIso_naturality R (B.transition h).hom 1 (by omega)
  simp only [Int.reduceAdd, Int.reduceNeg] at hf ht
  apply (cancel_mono (postnikovUpperClassLayerHomologyIso R (B.obj j).obj 1 (by omega)).hom).1
  rw [Category.assoc, hf, ← Category.assoc, d.candidateRoof_homology_action R, Category.assoc,
    d.coefficientHomologyAction_right R]
  exact ht.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
