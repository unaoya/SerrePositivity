module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightRestoreZero
public import
  SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceNativeModelHomotopy

/-!
概要：元の右像の相対模型上へ W と動く底を前合成し、両端の元の底射を回収する。
方針：relativeLeft と Γ の射影式を使い、relativeRight との厳密な整合を保つ。
規約：W の底を一定に置き換えない。使われ方：movingSourceNativeModelHomotopy の実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

local notation "α" => SquareZeroExtension.relativeLeft
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "β" => SquareZeroExtension.relativeRight
  (d.rightClassifyingLayer R) (d.rightImageClass R)
def rightWSourcePath : Path.Witness R (α ≫ ((postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom ≫ Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega))))
    (α ≫ d.fixedRightCompletedNativeSource R) where
  hom := α ≫ (postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom
  source_eq := Category.assoc _ _ _
  target_eq := by rw [Category.assoc, d.rightGammaSourceWitness_target R]

def rightWBasePath := α ≫
  (postnikovCommonRightGammaBasePath R f d.baseInverse d.layerInverse d.target_le).hom

lemma rightWSourcePath_projection : (d.rightWSourcePath R).hom ≫ Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
    d.rightWBasePath R := by
  change (α ≫ (postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom) ≫ _ = _
  rw [Category.assoc, postnikovCommonRightGammaSourceWitness_projection]
  rfl

lemma rightWBasePath_source : d.rightWBasePath R ≫ Path.source R (postnikov R (B.obj j).obj 1) =
    β ≫ postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le := by
  change (α ≫ _) ≫ _ = _
  rw [Category.assoc,
    (postnikovCommonRightGammaBasePath R f d.baseInverse d.layerInverse d.target_le).source_eq]
  rw [← postnikovCommonClassRightImageBase_composite, ← Category.assoc]
  change (α ≫ d.classProjection R) ≫ _ = _
  rw [← d.rightImageRelativeRight R]

lemma rightWBasePath_target : d.rightWBasePath R ≫ Path.target R (postnikov R (B.obj j).obj 1) =
    β ≫ postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le := by
  change (α ≫ _) ≫ _ = _
  rw [Category.assoc,
    (postnikovCommonRightGammaBasePath R f d.baseInverse d.layerInverse d.target_le).target_eq]
  rw [← postnikovCommonClassRightDenominatorBase_composite, ← Category.assoc]
  change (α ≫ d.classProjection R) ≫ _ = _
  rw [← d.rightImageRelativeRight R]

lemma rightWBasePath_zero : d.rightWBasePath R ≫
    Path.map R (postnikovTransition R (B.obj j).obj 1 0 (by omega)) =
    (β ≫ postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le) ≫
      Path.diagonal R (postnikov R (B.obj j).obj 0) := by
  have h := congrArg (fun t => α ≫ t)
    (postnikovCommonRightGammaBasePath_zero R f d.baseInverse d.layerInverse d.target_le)
  have h' : d.rightWBasePath R ≫
      Path.map R (postnikovTransition R (B.obj j).obj 1 0 (by omega)) =
      ((d.rightWBasePath R ≫ Path.source R (postnikov R (B.obj j).obj 1)) ≫
        postnikovTransition R (B.obj j).obj 1 0 (by omega)) ≫
          Path.diagonal R (postnikov R (B.obj j).obj 0) := by
    simpa only [rightWBasePath, Category.assoc] using h
  rw [h']
  rw [d.rightWBasePath_source R]
  simpa only [Category.assoc] using congrArg (fun t =>
    (β ≫ t) ≫ Path.diagonal R (postnikov R (B.obj j).obj 0))
    (postnikovCommonClassRightImageBase_zero R f d.baseInverse d.layerInverse d.target_le)

lemma rightWClass_projection : ((d.rightWSourcePath R).hom ≫ Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))) ≫
    Path.map R (SquareZero.projection _ _) = d.rightWBasePath R := by
  rw [Category.assoc, ← Path.map_comp, postnikovPerturbedClass_projection,
    d.rightWSourcePath_projection R]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
