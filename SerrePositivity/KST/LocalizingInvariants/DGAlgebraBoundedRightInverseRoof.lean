module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBoundedDerivedPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofConjugationPath

/-!
概要：二切断の実右逆 roof を、下界 −2 の元の代数間の実右逆へ戻す。
方針：元の切断商の正方形に沿って roof を移し、準同型の先の経路を反映する。
規約：右経路を局所化後の一致で代用しない。使われ方：非正次数対角の実右逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}
  {f : LevelHom A B} {i m : ℕ} {hi : i ≤ m}
  (c : NativeRightInverseRoof R (f.map (postnikovFunctor R 2)) i m hi)
  (hA : (A.obj i).obj.X.IsGE (-2)) (hB : (B.obj i).obj.X.IsGE (-2))

def NativeRightInverseRoof.ofPostnikovTwoBounded :
    NativeRightInverseRoof R (f.map (nonpositiveInclusion R)) i m hi := by
  let a := postnikovQuotient R (A.obj i).obj 2
  let b := postnikovQuotient R (B.obj m).obj 2
  let p := postnikovQuotient R (B.obj i).obj 2
  have ha : QuasiIso a.hom := postnikovQuotient_quasiIso R _ 2 hA
  have hp : QuasiIso p.hom := postnikovQuotient_quasiIso R _ 2 hB
  let r := RoofConjugation.roof R c.roof b a ha
  let v := RoofConjugation.rightPathAfterComparison R c.roof b a ha (f.app i).hom
    (postnikovMap R (f.app i).hom 2) p (B.transition hi).hom
    (postnikovMap R (B.transition hi).hom 2)
    (postnikovQuotient_naturality R (f.app i).hom 2).symm
    (postnikovQuotient_naturality R (B.transition hi).hom 2) c.rightPath
  let v' : Path.Witness R
      (((r.cellRefinement R 1).numerator ≫ (f.app i).hom) ≫ p)
      (((r.cellRefinement R 1).denominator ≫ (B.transition hi).hom) ≫ p) :=
    ⟨v.hom, v.source_eq.trans (Category.assoc _ _ _).symm,
      v.target_eq.trans (Category.assoc _ _ _).symm⟩
  exact ⟨(r.cellRefinement R 1).cellRefinement R 4,
    SurjectiveRoof.cellReflectEquation R (r.cellRefinement R 1) (f.app i).hom
      (B.transition hi).hom p hp v'⟩

lemma exists_boundedNativeRightInverseRoof (f : LevelHom A B)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-2)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-2))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1)))
    (h₂ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, Nonempty (NativeRightInverseRoof R (f.map (nonpositiveInclusion R)) i m hi) := by
  obtain ⟨m, hi, ⟨c⟩⟩ := exists_postnikovTwoNativeRightInverseRoof R f h₀ h₁ h₂ i
  exact ⟨m, hi, ⟨c.ofPostnikovTwoBounded R (hA i) (hB i)⟩⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
