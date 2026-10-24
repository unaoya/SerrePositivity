module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteDiagonalDefect
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofDiagonalCancellation

/-!
概要：対角の実右逆を元の左欠損に適用し、元の源への遷移後の実左経路を構成する。
方針：元の欠損対を対角 roof の分母へ持ち上げ、二重 cell 上の対角消去を前合成する。
規約：f の準同型性は要求しない。使われ方：両三角形を持つ元の有限切断逆。
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
  (f : LevelHom A B) {i m k : ℕ} {him : i ≤ m} {hmk : m ≤ k}
  (q : NativeRightInverseRoof R ((postnikovFiniteNonpositiveDiagonal R cutoff f).map
    (nonpositiveInclusion R)) i m him)
  (c : NativeRightInverseRoof R (f.map (postnikovFunctor R cutoff)) m k hmk)

def postnikovFiniteDiagonalCancellation : Path.Witness R
    ((q.roof.cellRefinement R 2).denominator ≫
      (((postnikovFiniteDiagonalTarget R cutoff f).transition him).hom ≫ postnikovFiniteDiagonalLeft R cutoff f i))
    ((q.roof.cellRefinement R 2).denominator ≫
      (((postnikovFiniteDiagonalTarget R cutoff f).transition him).hom ≫ postnikovFiniteDiagonalRight R cutoff f i)) :=
  SurjectiveRoof.diagonalCancellation R ((postnikovFiniteNonpositiveDiagonal R cutoff f).app i).hom
    (postnikovFiniteDiagonalLeft R cutoff f i) (postnikovFiniteDiagonalRight R cutoff f i)
    (postnikovFiniteNonpositiveDiagonal_left R cutoff f i) (postnikovFiniteNonpositiveDiagonal_right R cutoff f i)
    q.roof ((postnikovFiniteDiagonalTarget R cutoff f).transition him).hom q.rightPath

lemma postnikovFiniteDiagonalRefinedDenominator_surjective (degree : ℤ) :
    Function.Surjective ((q.roof.cellRefinement R 2).denominator.hom.f degree) := by
  have := (q.roof.cellRefinement R 2).denominator_epi
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

def postnikovFiniteDiagonalReflectionLift : cellResolution R (c.nonpositiveSource R) ⟶
    (q.roof.cellRefinement R 2).apex :=
  cellResolutionMapLift R (postnikovFiniteDefectPair R cutoff f c) (q.roof.cellRefinement R 2).denominator
    (postnikovFiniteDiagonalRefinedDenominator_surjective R cutoff f q)
    (q.roof.cellRefinement R 2).denominator_quasiIso

lemma postnikovFiniteDiagonalReflectionLift_denominator :
    postnikovFiniteDiagonalReflectionLift R cutoff f q c ≫ (q.roof.cellRefinement R 2).denominator =
      cellAugmentation R (c.nonpositiveSource R) ≫ postnikovFiniteDefectPair R cutoff f c :=
  cellResolutionMapLift_projection R _ _ _ _

def postnikovFiniteDiagonalLeftReflection : Path.Witness R
    (cellAugmentation R (c.nonpositiveSource R) ≫
      ((c.sourceLift R ≫ c.roof.numerator) ≫ postnikovMap R (A.transition him).hom cutoff))
    (cellAugmentation R (c.nonpositiveSource R) ≫
      (c.sourceProjection R ≫ postnikovMap R (A.transition (him.trans hmk)).hom cutoff)) := by
  let w := (postnikovFiniteDiagonalCancellation R cutoff f q).precomp
    (postnikovFiniteDiagonalReflectionLift R cutoff f q c)
  refine ⟨w.hom, w.source_eq.trans ?_, w.target_eq.trans ?_⟩
  · rw [← Category.assoc, postnikovFiniteDiagonalReflectionLift_denominator,
      Category.assoc, postnikovFiniteDiagonalLeft_naturality]
    simpa only [Category.assoc] using congrArg (fun t =>
      cellAugmentation R (c.nonpositiveSource R) ≫ (t ≫ postnikovMap R (A.transition him).hom cutoff))
      (postnikovFiniteDefectPair_left R cutoff f c)
  · rw [← Category.assoc, postnikovFiniteDiagonalReflectionLift_denominator,
      Category.assoc, postnikovFiniteDiagonalRight_naturality]
    have ht : postnikovMap R (A.transition hmk).hom cutoff ≫
        postnikovMap R (A.transition him).hom cutoff =
          postnikovMap R (A.transition (him.trans hmk)).hom cutoff :=
      (A.map (postnikovFunctor R cutoff)).transition_comp hmk him
    have he := congrArg (fun t => cellAugmentation R (c.nonpositiveSource R) ≫
      (t ≫ postnikovMap R (A.transition him).hom cutoff)) (postnikovFiniteDefectPair_right R cutoff f c)
    simp only [Category.assoc] at he
    exact he.trans (congrArg (fun t => cellAugmentation R (c.nonpositiveSource R) ≫
      (c.sourceProjection R ≫ t)) ht)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
