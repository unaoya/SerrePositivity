module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCoefficientTriangles
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCandidateLayerValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationLayers

/-!
概要：元の τₙ₊₁ 代数射と実候補 roof の H⁻⁽ⁿ⁺¹⁾ 作用が、両順序で元の遷移と一致する。
方針：同じ係数 Γ の両三角形を、元の上段層同型の自然性を介して移す。
規約：ホモロジーの両三角形であり、実代数射の両逆をまだ主張しない。
使われ方：次段候補の両ホモロジー三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

lemma candidateRoof_homology_action :
    (d.candidateRoof R).homologyValue R (-(n + 1)) ≫
      (postnikovUpperClassLayerHomologyIso R (A.obj j).obj n hn).hom =
    (postnikovUpperClassLayerHomologyIso R
      (B.obj d.layerInverse.zero.stage).obj n hn).hom ≫ d.coefficientHomologyAction R := by
  simpa only [coefficientHomologyAction, Category.assoc] using d.candidateRoof_homology_layer R

lemma candidateRoof_homology_left :
    homologyMap (postnikovMap R (f.app d.layerInverse.zero.stage).hom (n + 1)).hom (-(n + 1)) ≫
      (d.candidateRoof R).homologyValue R (-(n + 1)) = homologyMap (postnikovMap R
      (A.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom (n + 1)).hom (-(n + 1)) := by
  let h := d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
  have hf := postnikovUpperClassLayerHomologyIso_naturality R
    (f.app d.layerInverse.zero.stage).hom n hn
  have ht := postnikovUpperClassLayerHomologyIso_naturality R (A.transition h).hom n hn
  apply (cancel_mono (postnikovUpperClassLayerHomologyIso R (A.obj j).obj n hn).hom).1
  rw [Category.assoc, d.candidateRoof_homology_action R, ← Category.assoc, hf, Category.assoc,
    d.coefficientHomologyAction_left R]
  exact ht.symm

lemma candidateRoof_homology_right : (d.candidateRoof R).homologyValue R (-(n + 1)) ≫
    homologyMap (postnikovMap R (f.app j).hom (n + 1)).hom (-(n + 1)) = homologyMap (postnikovMap R
      (B.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom (n + 1)).hom (-(n + 1)) := by
  let h := d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
  have hf := postnikovUpperClassLayerHomologyIso_naturality R (f.app j).hom n hn
  have ht := postnikovUpperClassLayerHomologyIso_naturality R (B.transition h).hom n hn
  apply (cancel_mono (postnikovUpperClassLayerHomologyIso R (B.obj j).obj n hn).hom).1
  rw [Category.assoc, hf, ← Category.assoc, d.candidateRoof_homology_action R, Category.assoc,
    d.coefficientHomologyAction_right R]
  exact ht.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
