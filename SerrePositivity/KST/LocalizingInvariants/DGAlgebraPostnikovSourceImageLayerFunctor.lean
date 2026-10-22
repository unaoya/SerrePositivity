module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageHomologySquare

/-!
概要：源側像拡大の層と元のホモロジー像の図式を、実関手間の自然同型として比較する。
方針：元のホモロジー関手の矢印関手と像関手を合成し、構成済みの正方形の式を包装。
規約：対象ごとの同型だけで自然性を代用しない。使われ方：LT の層の図式と pro 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def nonpositiveAlgebraHomologyFunctor (j : ℤ) : NonpositiveAlgebra R ⥤ ModuleCat.{u} R :=
  nonpositiveInclusion R ⋙ Mon.forget (Complex R) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) j

def postnikovHomologyImageArrowFunctor (n : ℤ) :
    Arrow (NonpositiveAlgebra R) ⥤ ModuleCat.{u} R :=
  (nonpositiveAlgebraHomologyFunctor R (-(n + 1))).mapArrow ⋙ im

variable (n : ℤ) (hn : 0 ≤ n)

def postnikovSourceImageLayerNatIso : postnikovSourceImageArrowFunctor R n hn ⋙
    Mon.forget (Complex R) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) (-(n + 1)) ≅
      postnikovHomologyImageArrowFunctor R n :=
  NatIso.ofComponents (fun f => postnikovSourceImageLayerHomologyIso R f.hom.hom n hn)
    (fun {_ _} a => postnikovSourceImageLayerHomologyIso_square R n hn _ _ a.left.hom a.right.hom
      (postnikovSourceImageArrow_condition R a))

def postnikovSourceImageArrowProjection : postnikovSourceImageArrowFunctor R n hn ⟶
    (Arrow.leftFunc : Arrow (NonpositiveAlgebra R) ⥤ NonpositiveAlgebra R) ⋙
      postnikovFunctor R n where
  app f := postnikovSourceImageProjection R f.hom.hom n hn
  naturality {_ _} a := postnikovSourceImageExtensionSquareMap_right R n hn _ _
    a.left.hom a.right.hom (postnikovSourceImageArrow_condition R a)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
