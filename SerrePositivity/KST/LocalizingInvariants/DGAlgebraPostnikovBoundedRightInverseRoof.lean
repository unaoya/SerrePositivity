module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorNativeRightInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofConjugationPath

/-!
概要：有限切断の実右逆 roof を、同じ下界を持つ元の代数間の実右逆へ戻す。
方針：元の切断商の正方形に沿って roof を移し、準同型の先の経路を反映する。
規約：切断次数は任意整数で、cell 細分の回数と区別する。
使われ方：有限 Postnikov 帰納での非正次数対角の実右逆。
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
variable (R : Type u) [CommRing R] (cutoff : ℤ) {A B : Tower (NonpositiveAlgebra R)}
  {f : LevelHom A B} {i m : ℕ} {hi : i ≤ m}
  (c : NativeRightInverseRoof R (f.map (postnikovFunctor R cutoff)) i m hi)
  (hA : (A.obj i).obj.X.IsGE (-cutoff)) (hB : (B.obj i).obj.X.IsGE (-cutoff))

def NativeRightInverseRoof.ofPostnikovBounded :
    NativeRightInverseRoof R (f.map (nonpositiveInclusion R)) i m hi := by
  let a := postnikovQuotient R (A.obj i).obj cutoff
  let b := postnikovQuotient R (B.obj m).obj cutoff
  let p := postnikovQuotient R (B.obj i).obj cutoff
  have ha : QuasiIso a.hom := postnikovQuotient_quasiIso R _ cutoff hA
  have hp : QuasiIso p.hom := postnikovQuotient_quasiIso R _ cutoff hB
  let r := RoofConjugation.roof R c.roof b a ha
  let v := RoofConjugation.rightPathAfterComparison R c.roof b a ha (f.app i).hom
    (postnikovMap R (f.app i).hom cutoff) p (B.transition hi).hom
    (postnikovMap R (B.transition hi).hom cutoff)
    (postnikovQuotient_naturality R (f.app i).hom cutoff).symm
    (postnikovQuotient_naturality R (B.transition hi).hom cutoff) c.rightPath
  let v' : Path.Witness R
      (((r.cellRefinement R 1).numerator ≫ (f.app i).hom) ≫ p)
      (((r.cellRefinement R 1).denominator ≫ (B.transition hi).hom) ≫ p) :=
    ⟨v.hom, v.source_eq.trans (Category.assoc _ _ _).symm,
      v.target_eq.trans (Category.assoc _ _ _).symm⟩
  exact ⟨(r.cellRefinement R 1).cellRefinement R 4,
    SurjectiveRoof.cellReflectEquation R (r.cellRefinement R 1) (f.app i).hom
      (B.transition hi).hom p hp v'⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
