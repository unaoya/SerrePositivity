module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageLevelValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackProjectionProGroups
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackSquareLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverLiftNaturality

/-!
概要：元の未切断の代数の塔の射を、有限像模型を底とする実レベル射で因子分解する。
方針：像模型と元の標的の実 pullback 模型を作り、源からの射を非正次数 cover へ上げる。
規約：元のレベル射との合成は厳密等式。使われ方：連結なレベル表示の元の塔への復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovConnectedLevel
open ProExcision
variable (R : Type u) [CommRing R] (X : Tower (Arrow (NonpositiveAlgebra R)))
  (n : ℤ) (hn : 0 ≤ n)

def source : Tower (NonpositiveAlgebra R) := X.map Arrow.leftFunc

def target : Tower (NonpositiveAlgebra R) := X.map Arrow.rightFunc

def original : LevelHom (source R X) (target R X) := TowerDiagram.mapNat X Arrow.leftToRight

def rawMiddle : Tower (Mon (Complex R)) := HomotopyPullbackModel.modelTower R
  (PostnikovImagePro.right R X n hn) (PostnikovImagePro.targetQuotient R X n)

def rawRight : LevelHom (rawMiddle R X n hn) (PostnikovImagePro.target R X) :=
  HomotopyPullbackModel.rightProjection R _ _

lemma rawSquare :
    ((PostnikovImagePro.sourceQuotient R X n).comp (PostnikovImagePro.left R X n hn)).comp
        (PostnikovImagePro.right R X n hn) =
      (PostnikovImagePro.original R X).comp (PostnikovImagePro.targetQuotient R X n) := by
  apply ProSpectrum.levelHom_ext
  intro i
  change (postnikovQuotient R (X.obj i).left.obj (n + 1) ≫
      postnikovImageFactorisationSource R (X.obj i).hom.hom n hn) ≫
        postnikovImageFactorisationTarget R (X.obj i).hom.hom n hn =
      (X.obj i).hom.hom ≫ postnikovQuotient R (X.obj i).right.obj (n + 1)
  rw [Category.assoc, postnikovImageFactorisation_fac, postnikovQuotient_naturality]

def rawLeft : LevelHom (PostnikovImagePro.source R X) (rawMiddle R X n hn) :=
  HomotopyPullbackModel.squareLift R _ _
    ((PostnikovImagePro.sourceQuotient R X n).comp (PostnikovImagePro.left R X n hn))
    (PostnikovImagePro.original R X) (rawSquare R X n hn)

lemma raw_fac : (rawLeft R X n hn).comp (rawRight R X n hn) = PostnikovImagePro.original R X :=
  HomotopyPullbackModel.squareLift_comp_right R _ _ _ _ _

def middle : Tower (NonpositiveAlgebra R) :=
  (rawMiddle R X n hn).map (connectiveCoverNonpositive R)

local instance source_nonpositive (i : ℕ) :
    ((PostnikovImagePro.source R X).obj i).X.IsStrictlyLE 0 := (X.obj i).left.property

def left : LevelHom (source R X) (middle R X n hn) where
  app i := ObjectProperty.homMk (connectiveCoverLift R ((rawLeft R X n hn).app i))
  naturality h := by
    apply ObjectProperty.hom_ext
    exact connectiveCoverLift_naturality R ((rawLeft R X n hn).app _)
      ((rawLeft R X n hn).app _) ((PostnikovImagePro.source R X).transition h)
      ((rawMiddle R X n hn).transition h) ((rawLeft R X n hn).naturality h)

def right : LevelHom (middle R X n hn) (target R X) where
  app i := ObjectProperty.homMk
    (connectiveCoverInclusion R ((rawMiddle R X n hn).obj i) ≫ (rawRight R X n hn).app i)
  naturality h := by
    apply ObjectProperty.hom_ext
    exact ((coverTowerCounit R (rawMiddle R X n hn)).comp (rawRight R X n hn)).naturality h

lemma fac : (left R X n hn).comp (right R X n hn) = original R X := by
  apply ProSpectrum.levelHom_ext
  intro i
  apply ObjectProperty.hom_ext
  change connectiveCoverLift R ((rawLeft R X n hn).app i) ≫
    (connectiveCoverInclusion R ((rawMiddle R X n hn).obj i) ≫
      (rawRight R X n hn).app i) = (X.obj i).hom.hom
  rw [← Category.assoc, connectiveCoverLift_inclusion]
  exact congrArg (fun t => t.app i) (raw_fac R X n hn)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovConnectedLevel
