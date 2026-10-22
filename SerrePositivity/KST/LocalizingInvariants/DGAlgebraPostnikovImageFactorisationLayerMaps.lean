module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationLayerFunctor

/-!
概要：実因子分解の二つの自然変換を、元のホモロジー像の自然な射影・包含へ比較する。
方針：上段と中間代数の層自然同型を使い、構成済みの元の二射の成分計算を包装する。
規約：自然変換全体の等式を供給。使われ方：LT の実層図式と像分解の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)

def postnikovUpperClassLayerNatIso : postnikovFunctor R (n + 1) ⋙ Mon.forget (Complex R) ⋙
    homologyFunctor (ModuleCat R) (.up ℤ) (-(n + 1)) ≅
      nonpositiveAlgebraHomologyFunctor R (-(n + 1)) :=
  NatIso.ofComponents (fun B => postnikovUpperClassLayerHomologyIso R B.obj n hn)
    (fun {_ _} f => postnikovUpperClassLayerHomologyIso_naturality R f.hom n hn)

def postnikovHomologyImageArrowProjection :
    (Arrow.leftFunc : Arrow (NonpositiveAlgebra R) ⥤ NonpositiveAlgebra R) ⋙
      nonpositiveAlgebraHomologyFunctor R (-(n + 1)) ⟶ postnikovHomologyImageArrowFunctor R n where
  app f := factorThruImage (homologyMap f.hom.hom.hom (-(n + 1)))
  naturality {f g} a := (image.factor_map (postnikovHomologySquare R n f.hom.hom g.hom.hom
    a.left.hom a.right.hom (postnikovSourceImageArrow_condition R a))).symm

def postnikovHomologyImageArrowInclusion : postnikovHomologyImageArrowFunctor R n ⟶
    (Arrow.rightFunc : Arrow (NonpositiveAlgebra R) ⥤ NonpositiveAlgebra R) ⋙
      nonpositiveAlgebraHomologyFunctor R (-(n + 1)) where
  app f := image.ι (homologyMap f.hom.hom.hom (-(n + 1)))
  naturality {f g} a := image.map_ι (postnikovHomologySquare R n f.hom.hom g.hom.hom
    a.left.hom a.right.hom (postnikovSourceImageArrow_condition R a))

lemma postnikovImageFactorisationArrowSource_layer :
    CategoryTheory.Functor.whiskerRight (postnikovImageFactorisationArrowSource R n hn)
      (Mon.forget (Complex R) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) (-(n + 1))) ≫
        (postnikovImageFactorisationLayerNatIso R n hn).hom =
    CategoryTheory.Functor.whiskerLeft Arrow.leftFunc (postnikovUpperClassLayerNatIso R n hn).hom ≫
      postnikovHomologyImageArrowProjection R n := by
  apply NatTrans.ext
  funext f
  change homologyMap (postnikovImageFactorisationSource R f.hom.hom n hn).hom (-(n + 1)) ≫
    ((postnikovImageFactorisationLayerNatIso R n hn).app f).hom = _
  rw [postnikovImageFactorisationLayerNatIso_app_hom]
  exact postnikovImageFactorisationSource_layer R f.hom.hom n hn

lemma postnikovImageFactorisationArrowTarget_layer :
    CategoryTheory.Functor.whiskerRight (postnikovImageFactorisationArrowTarget R n hn)
      (Mon.forget (Complex R) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) (-(n + 1))) ≫
        CategoryTheory.Functor.whiskerLeft Arrow.rightFunc
          (postnikovUpperClassLayerNatIso R n hn).hom =
      (postnikovImageFactorisationLayerNatIso R n hn).hom ≫
        postnikovHomologyImageArrowInclusion R n := by
  apply NatTrans.ext
  funext f
  change homologyMap (postnikovImageFactorisationTarget R f.hom.hom n hn).hom (-(n + 1)) ≫
    (postnikovUpperClassLayerHomologyIso R f.right.obj n hn).hom =
      ((postnikovImageFactorisationLayerNatIso R n hn).app f).hom ≫ _
  rw [postnikovImageFactorisationLayerNatIso_app_hom]
  exact postnikovImageFactorisationTarget_layer R f.hom.hom n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
