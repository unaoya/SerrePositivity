module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationNatural
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageLayerFunctor

/-!
概要：元の標的までの実因子分解の層を、元のホモロジー像関手と自然同型で比較する。
方針：元の準同型比較の自然変換をホモロジーへ送り、源側像拡大の層自然同型と合成する。
規約：既存の対象ごとの層同型と一致。使われ方：LT の実図式の層比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)

def postnikovImageFactorisationComparisonHomologyIso (j : ℤ) :
    postnikovImageFactorisationArrowFunctor R n hn ⋙ Mon.forget (Complex R) ⋙
      homologyFunctor (ModuleCat R) (.up ℤ) j ≅
    postnikovSourceImageArrowFunctor R n hn ⋙ Mon.forget (Complex R) ⋙
      homologyFunctor (ModuleCat R) (.up ℤ) j :=
  NatIso.ofComponents (fun f => by
    have := postnikovImageFactorisationArrowComparison_quasiIso R n hn f
    exact asIso (homologyMap ((postnikovImageFactorisationArrowComparison R n hn).app f).hom j))
    (fun {f g} a => by
      have h : ((postnikovImageFactorisationArrowFunctor R n hn).map a).hom ≫
          ((postnikovImageFactorisationArrowComparison R n hn).app g).hom =
        ((postnikovImageFactorisationArrowComparison R n hn).app f).hom ≫
          ((postnikovSourceImageArrowFunctor R n hn).map a).hom :=
        congrArg Mon.Hom.hom ((postnikovImageFactorisationArrowComparison R n hn).naturality a)
      change homologyMap ((postnikovImageFactorisationArrowFunctor R n hn).map a).hom j ≫
        homologyMap ((postnikovImageFactorisationArrowComparison R n hn).app g).hom j =
          homologyMap ((postnikovImageFactorisationArrowComparison R n hn).app f).hom j ≫
            homologyMap ((postnikovSourceImageArrowFunctor R n hn).map a).hom j
      rw [← homologyMap_comp, ← homologyMap_comp]
      exact congrArg (fun z => homologyMap z j) h)

def postnikovImageFactorisationLayerNatIso : postnikovImageFactorisationArrowFunctor R n hn ⋙
    Mon.forget (Complex R) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) (-(n + 1)) ≅
      postnikovHomologyImageArrowFunctor R n :=
  postnikovImageFactorisationComparisonHomologyIso R n hn (-(n + 1)) ≪≫
    postnikovSourceImageLayerNatIso R n hn

lemma postnikovImageFactorisationLayerNatIso_app_hom (f : Arrow (NonpositiveAlgebra R)) :
    ((postnikovImageFactorisationLayerNatIso R n hn).app f).hom =
      (postnikovImageFactorisationLayerHomologyIso R f.hom.hom n hn).hom := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
