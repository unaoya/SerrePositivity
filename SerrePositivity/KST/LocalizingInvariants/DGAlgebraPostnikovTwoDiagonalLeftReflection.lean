module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoDiagonalDefect
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofDiagonalCancellation

/-!
概要：対角の実右逆を元の左欠損に適用し、元の源への遷移後の実左経路を構成する。
方針：元の欠損対を対角 roof の分母へ持ち上げ、二重 cell 上の対角消去を前合成する。
規約：f の準同型性は要求しない。使われ方：両三角形を持つ元の二切断逆。
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
  (f : LevelHom A B) {i m k : ℕ} {him : i ≤ m} {hmk : m ≤ k}
  (q : NativeRightInverseRoof R ((postnikovTwoNonpositiveDiagonal R f).map
    (nonpositiveInclusion R)) i m him)
  (c : NativeRightInverseRoof R (f.map (postnikovFunctor R 2)) m k hmk)

def postnikovTwoDiagonalCancellation : Path.Witness R
    ((q.roof.cellRefinement R 2).denominator ≫
      (((postnikovTwoDiagonalTarget R f).transition him).hom ≫ postnikovTwoDiagonalLeft R f i))
    ((q.roof.cellRefinement R 2).denominator ≫
      (((postnikovTwoDiagonalTarget R f).transition him).hom ≫ postnikovTwoDiagonalRight R f i)) :=
  SurjectiveRoof.diagonalCancellation R ((postnikovTwoNonpositiveDiagonal R f).app i).hom
    (postnikovTwoDiagonalLeft R f i) (postnikovTwoDiagonalRight R f i)
    (postnikovTwoNonpositiveDiagonal_left R f i) (postnikovTwoNonpositiveDiagonal_right R f i)
    q.roof ((postnikovTwoDiagonalTarget R f).transition him).hom q.rightPath

lemma postnikovTwoDiagonalRefinedDenominator_surjective (n : ℤ) :
    Function.Surjective ((q.roof.cellRefinement R 2).denominator.hom.f n) := by
  have := (q.roof.cellRefinement R 2).denominator_epi
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

def postnikovTwoDiagonalReflectionLift : cellResolution R (c.nonpositiveSource R) ⟶
    (q.roof.cellRefinement R 2).apex :=
  cellResolutionMapLift R (postnikovTwoDefectPair R f c) (q.roof.cellRefinement R 2).denominator
    (postnikovTwoDiagonalRefinedDenominator_surjective R f q)
    (q.roof.cellRefinement R 2).denominator_quasiIso

lemma postnikovTwoDiagonalReflectionLift_denominator :
    postnikovTwoDiagonalReflectionLift R f q c ≫ (q.roof.cellRefinement R 2).denominator =
      cellAugmentation R (c.nonpositiveSource R) ≫ postnikovTwoDefectPair R f c :=
  cellResolutionMapLift_projection R _ _ _ _

def postnikovTwoDiagonalLeftReflection : Path.Witness R
    (cellAugmentation R (c.nonpositiveSource R) ≫
      ((c.sourceLift R ≫ c.roof.numerator) ≫ postnikovMap R (A.transition him).hom 2))
    (cellAugmentation R (c.nonpositiveSource R) ≫
      (c.sourceProjection R ≫ postnikovMap R (A.transition (him.trans hmk)).hom 2)) := by
  let w := (postnikovTwoDiagonalCancellation R f q).precomp
    (postnikovTwoDiagonalReflectionLift R f q c)
  refine ⟨w.hom, w.source_eq.trans ?_, w.target_eq.trans ?_⟩
  · rw [← Category.assoc, postnikovTwoDiagonalReflectionLift_denominator,
      Category.assoc, postnikovTwoDiagonalLeft_naturality]
    simpa only [Category.assoc] using congrArg (fun t =>
      cellAugmentation R (c.nonpositiveSource R) ≫ (t ≫ postnikovMap R (A.transition him).hom 2))
      (postnikovTwoDefectPair_left R f c)
  · rw [← Category.assoc, postnikovTwoDiagonalReflectionLift_denominator,
      Category.assoc, postnikovTwoDiagonalRight_naturality]
    have ht : postnikovMap R (A.transition hmk).hom 2 ≫
        postnikovMap R (A.transition him).hom 2 =
          postnikovMap R (A.transition (him.trans hmk)).hom 2 :=
      (A.map (postnikovFunctor R 2)).transition_comp hmk him
    have he := congrArg (fun t => cellAugmentation R (c.nonpositiveSource R) ≫
      (t ≫ postnikovMap R (A.transition him).hom 2)) (postnikovTwoDefectPair_right R f c)
    simp only [Category.assoc] at he
    exact he.trans (congrArg (fun t => cellAugmentation R (c.nonpositiveSource R) ≫
      (c.sourceProjection R ≫ t)) ht)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
