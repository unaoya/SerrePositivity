module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassModelValue

/-!
概要：実次段切断候補の底への作用を、元の実下段切断逆 roof の値に同定する。
方針：両端の準同型逆 roof の脚の自然性と、class 模型射の元の右脚を組み合わせる。
規約：全準同型反転関手に対する式。次段切断全体の逆三角形とは区別する。
使われ方：次段候補と下段逆の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L)

lemma sourceUpperRoof_value_base_comp :
    SurjectiveRoof.value R L hL (d.sourceUpperRoof R) ≫
      L.map (HomotopyPullbackModel.right R (d.sourceClass R) _ ≫
        (d.lowerBaseInverse R).roof.denominator) =
      L.map (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) := by
  let p : d.sourceModel R ⟶ d.classBase R := HomotopyPullbackModel.right R _ _
  let r : d.originalSourceModel R ⟶ postnikov R (B.obj d.layerInverse.zero.stage).obj n :=
    HomotopyPullbackModel.right R _ _
  have hN := SurjectiveRoof.inverse_value_naturality R (d.sourceToOriginalModel R) L
    (d.sourceToOriginalModel_quasiIso R) (p ≫ (d.lowerBaseInverse R).roof.denominator) r
      (d.sourceToOriginalModel_right R) hL
  rw [sourceUpperRoof, SurjectiveRoof.comp_value, SurjectiveRoof.ofHom_value,
    Category.assoc, hN, ← L.map_comp, postnikovHomotopyPullbackComparison_right]

lemma sourceUpperRoof_value_base :
    SurjectiveRoof.value R L hL (d.sourceUpperRoof R) ≫
      L.map (HomotopyPullbackModel.right R (d.sourceClass R) _) =
    L.map (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
      SurjectiveRoof.value R L hL (SurjectiveRoof.ofQuasiIsoInverse R
        (d.lowerBaseInverse R).roof.denominator (d.lowerBaseInverse R).roof.denominator_quasiIso)
    := by
  have := hL _ (d.lowerBaseInverse R).roof.denominator_quasiIso
  apply (cancel_mono (L.map (d.lowerBaseInverse R).roof.denominator)).1
  rw [Category.assoc, ← L.map_comp, d.sourceUpperRoof_value_base_comp R L hL,
    Category.assoc, SurjectiveRoof.inverse_value_comp, Category.comp_id]

lemma targetUpperRoof_value_base :
    SurjectiveRoof.value R L hL (targetUpperRoof (A := A) (j := j) R) ≫
      L.map (postnikovTransition R (A.obj j).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) =
    L.map (HomotopyPullbackModel.right R
      (postnikovPerturbedClass R (A.obj j).obj n hn) _) :=
  SurjectiveRoof.inverse_value_naturality R
    (postnikovHomotopyPullbackComparison R (A.obj j).obj n hn) L
    (postnikovHomotopyPullbackComparison_quasiIso R (A.obj j).obj n hn) _ _
    (postnikovHomotopyPullbackComparison_right R (A.obj j).obj n hn) hL

/-- 元の実候補 roof の τₙ への射影は、同じ底の実逆 roof の値と可換。 -/
lemma candidateRoof_value_base : SurjectiveRoof.value R L hL (d.candidateRoof R) ≫
    L.map (postnikovTransition R (A.obj j).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) =
      L.map (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
        SurjectiveRoof.value R L hL (d.lowerBaseInverse R).roof := by
  simp only [candidateRoof, SurjectiveRoof.nonpositiveNormalization_value, rawCandidateRoof,
    SurjectiveRoof.comp_value, Category.assoc]
  rw [targetUpperRoof_value_base R L hL, d.classModelCandidateRoof_value_right R L hL,
    ← Category.assoc, d.sourceUpperRoof_value_base R L hL]
  change (L.map (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
    SurjectiveRoof.value R L hL (SurjectiveRoof.ofQuasiIsoInverse R
      (d.lowerBaseInverse R).roof.denominator (d.lowerBaseInverse R).roof.denominator_quasiIso)) ≫
      L.map (d.lowerBaseInverse R).roof.numerator = _
  rw [Category.assoc, SurjectiveRoof.value_eq_inverse_denominator]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
