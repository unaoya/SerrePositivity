module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectNativeInput

/-!
概要：元の直接 source 経路の両端を、元の sourceCellMap と completed source で表示する。
方針：保存済みの両端式を束ね、元の全射と一定底式を保持する。
規約：経路は選び直さない。使われ方：元の相対模型への source ホモトピーの適用。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def fixedRightDirectSourceWitness : Path.Witness R (d.directNativeSource R)
    (d.fixedRightCompletedNativeSource R) where
  hom := (d.fixedRightDirectSourcePath R).hom
  source_eq := d.fixedRightDirectSourcePath_source R
  target_eq := d.fixedRightDirectSourcePath_target R

lemma fixedRightDirectSourceWitness_hom : (d.fixedRightDirectSourceWitness R).hom =
    (d.fixedRightDirectSourcePath R).hom := rfl

lemma fixedRightDirectSourceWitness_relative : (d.fixedRightDirectSourceWitness R).hom ≫
    Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
    (d.classProjection R ≫ postnikovCommonClassRightDenominatorBase R f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) := by
  rw [d.fixedRightDirectSourceWitness_hom R]
  exact d.fixedRightDirectSourcePath_relative R

lemma sourceRelativeRight_projection :
    SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      d.classProjection R := by
  rw [SquareZeroExtension.relativeRight_eq, d.sourceClass_projection R]

lemma fixedRightDirectSourceWitness_class_relative :
    ((d.fixedRightDirectSourceWitness R).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))) ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj j).obj 1)
        (directNativeLayer (B := B) (j := j) R)) =
    (d.classProjection R ≫ postnikovCommonClassRightDenominatorBase R f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) := by
  let h := (d.fixedRightDirectSourceWitness R).hom
  let f' := postnikovPerturbedClass R (B.obj j).obj 1 (by omega)
  let p := SquareZero.projection (postnikov R (B.obj j).obj 1)
    (directNativeLayer (B := B) (j := j) R)
  let h₀ := Category.assoc h (Path.map R f') (Path.map R p)
  let h₁ := congrArg (fun t => h ≫ t) (Path.map_comp R f' p).symm
  let h₂ := congrArg (fun t => h ≫ Path.map R t)
    (postnikovPerturbedClass_projection R (B.obj j).obj 1 (by omega))
  exact ((h₀.trans h₁).trans h₂).trans (d.fixedRightDirectSourceWitness_relative R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
