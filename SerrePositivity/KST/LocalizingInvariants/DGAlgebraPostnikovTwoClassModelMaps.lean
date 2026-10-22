module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassModels

/-!
概要：二切断 class 逆の係数模型射と、標準 class 模型へ向かう実準同型 zigzag を構成。
方針：元の係数射は厳密 cospan 射、class の経路は mapping-path の厳密化に渡す。
規約：四つの射とも元の右脚を保持。使われ方：元の二切断への実 roof 移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def sourceToImage : d.sourceModel R ⟶ d.imageModel R :=
  HomotopyPullbackModel.map R (d.sourceClass R) _ (d.imageClass R) _ (𝟙 (d.classSource R))
    (SquareZero.coefficientMap (d.classBase R) (d.classCoefficient R)) (𝟙 (d.classBase R))
    (Category.id_comp _) (by
      apply Mon.Hom.ext
      change (𝟙 (d.classBase R).X) ≫ biprod.inl =
        biprod.inl ≫ biprod.map (𝟙 (d.classBase R).X) (d.classCoefficient R).hom
      rw [biprod.inl_map, Category.id_comp])

def imageToPath : d.imageModel R ⟶ d.pathModel R :=
  PathCospanComparison.originalToPath R
    (SquareZero.zeroSection (d.classBase R) (d.numeratorLayer R)) (d.imageClass R)

def targetToPath : d.targetComposedModel R ⟶ d.pathModel R :=
  PathCospanComparison.composedToPath R (d.targetClass R)
    (SquareZero.zeroSection (d.classBase R) (d.numeratorLayer R)) (d.imageClass R)
    (𝟙 (d.classSource R)) (d.comparisonPath R)

def targetToStandard : d.targetComposedModel R ⟶ d.targetModel R :=
  PathCospanComparison.composedToOriginal R (d.targetClass R)
    (SquareZero.zeroSection (d.classBase R) (d.numeratorLayer R)) (𝟙 (d.classSource R))

lemma imageToPath_quasiIso : QuasiIso (d.imageToPath R).hom :=
  PathCospanComparison.originalToPath_quasiIso R _ _

lemma targetToPath_quasiIso : QuasiIso (d.targetToPath R).hom :=
  PathCospanComparison.composedToPath_quasiIso R _ _ _ _ _

lemma targetToStandard_quasiIso : QuasiIso (d.targetToStandard R).hom :=
  PathCospanComparison.composedToOriginal_quasiIso R _ _ _ (quasiIso_of_isIso _)

lemma sourceToImage_right : d.sourceToImage R ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ :=
  (HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma sourceToImage_left : d.sourceToImage R ≫ HomotopyPullbackModel.left R _ _ =
    HomotopyPullbackModel.left R _ _ :=
  (HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma imageToPath_right : d.imageToPath R ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ := PathCospanComparison.originalToPath_right R _ _

lemma targetToPath_right : d.targetToPath R ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ := PathCospanComparison.composedToPath_right R _ _ _ _ _

lemma targetToStandard_right : d.targetToStandard R ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ := PathCospanComparison.composedToOriginal_right R _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
