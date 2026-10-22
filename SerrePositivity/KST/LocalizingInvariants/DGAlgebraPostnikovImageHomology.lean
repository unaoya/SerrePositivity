module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayerHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerImage

/-!
概要：元の shift 係数像のホモロジーを、元の代数射の下端ホモロジー像へ同定する。
方針：元の実 epi-mono 分解と shift 層の自然比較を、Arrow 圏の像関手で合成する。
規約：元の包含と射影の式を保持。使われ方：LT の像拡大の連結度計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n) (s : ℤ)

local instance imageHomologySourceUpper :
    (postnikovShiftedLayerBimodule R B n hn s).X.IsStrictlyLE (-(n + 1) - s) :=
  postnikovShiftedLayer_upperBound R B n hn s

local instance imageHomologyTargetLower :
    (bimoduleRestrict (postnikovMap R f n)
      (postnikovShiftedLayerBimodule R C n hn s)).X.IsStrictlyGE (-(n + 1) - s) :=
  postnikovShiftedLayer_lowerBound R C n hn s

def postnikovShiftedLayerHomologyArrowIso :
    Arrow.mk (homologyMap (postnikovShiftedLayerMap R B n hn s f).hom (-(n + 1) - s)) ≅
      Arrow.mk (homologyMap f.hom (-(n + 1))) :=
  Arrow.isoMk (postnikovShiftedLayerHomologyIso R B n hn s)
    (postnikovShiftedLayerHomologyIso R C n hn s)
    (postnikovShiftedLayerHomologyIso_naturality R B n hn s f).symm

def postnikovShiftedLayerImageHomologyIso :
    (postnikovShiftedLayerImage R f n hn s).X.homology (-(n + 1) - s) ≅
      image (homologyMap f.hom (-(n + 1))) :=
  DGBimoduleImage.homologyImageIso (postnikovShiftedLayerMap R B n hn s f) (-(n + 1) - s) ≪≫
    (im (C := ModuleCat.{u} R)).mapIso (postnikovShiftedLayerHomologyArrowIso R f n hn s)

lemma postnikovShiftedLayerImageHomologyIso_inclusion :
    (postnikovShiftedLayerImageHomologyIso R f n hn s).hom ≫
      image.ι (homologyMap f.hom (-(n + 1))) =
        homologyMap (postnikovShiftedLayerImageInclusion R f n hn s).hom (-(n + 1) - s) ≫
          (postnikovShiftedLayerHomologyIso R C n hn s).hom := by
  let e := DGBimoduleImage.homologyImageIso (postnikovShiftedLayerMap R B n hn s f)
    (-(n + 1) - s)
  let m := image.map (postnikovShiftedLayerHomologyArrowIso R f n hn s).hom
  have he : m ≫ image.ι (homologyMap f.hom (-(n + 1))) =
      image.ι (homologyMap (postnikovShiftedLayerMap R B n hn s f).hom (-(n + 1) - s)) ≫
        (postnikovShiftedLayerHomologyIso R C n hn s).hom :=
    image.map_ι (postnikovShiftedLayerHomologyArrowIso R f n hn s).hom
  exact (Category.assoc e.hom m _).trans ((congrArg (fun t => e.hom ≫ t) he).trans
    ((Category.assoc _ _ _).symm.trans (congrArg
      (fun t => t ≫ (postnikovShiftedLayerHomologyIso R C n hn s).hom)
      (DGBimoduleImage.homologyImageIso_inclusion _ _))))

lemma postnikovShiftedLayerImageHomologyIso_projection :
    homologyMap (postnikovShiftedLayerImageProjection R f n hn s).hom (-(n + 1) - s) ≫
      (postnikovShiftedLayerImageHomologyIso R f n hn s).hom =
        (postnikovShiftedLayerHomologyIso R B n hn s).hom ≫
          factorThruImage (homologyMap f.hom (-(n + 1))) := by
  let e := DGBimoduleImage.homologyImageIso (postnikovShiftedLayerMap R B n hn s f)
    (-(n + 1) - s)
  let m := image.map (postnikovShiftedLayerHomologyArrowIso R f n hn s).hom
  exact (Category.assoc _ e.hom m).symm.trans ((congrArg (fun t => t ≫ m)
    (DGBimoduleImage.homologyImageIso_projection (postnikovShiftedLayerMap R B n hn s f)
      (-(n + 1) - s))).trans (image.factor_map
        (postnikovShiftedLayerHomologyArrowIso R f n hn s).hom))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
