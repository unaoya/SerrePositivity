module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationSourceSquare
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationSuccessor

/-!
概要：元の上段の射を、実関手間の元の二つの自然変換として厳密に因子分解する。
方針：元の source・target・準同型比較の正方形自然性を、実自然変換へ包装する。
規約：合成は元の Postnikov 関手の矢印そのもの。使われ方：LT の連結な実図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)

def postnikovImageFactorisationArrowSource :
    (Arrow.leftFunc : Arrow (NonpositiveAlgebra R) ⥤ NonpositiveAlgebra R) ⋙
      postnikovFunctor R (n + 1) ⟶ postnikovImageFactorisationArrowFunctor R n hn where
  app f := postnikovImageFactorisationSource R f.hom.hom n hn
  naturality {_ _} a := postnikovImageFactorisationSource_square R n hn _ _
    a.left.hom a.right.hom (postnikovSourceImageArrow_condition R a)

def postnikovImageFactorisationArrowTarget : postnikovImageFactorisationArrowFunctor R n hn ⟶
    (Arrow.rightFunc : Arrow (NonpositiveAlgebra R) ⥤ NonpositiveAlgebra R) ⋙
      postnikovFunctor R (n + 1) where
  app f := postnikovImageFactorisationTarget R f.hom.hom n hn
  naturality {_ _} a := postnikovImageFactorisationSquareMap_target R n hn _ _
    a.left.hom a.right.hom (postnikovSourceImageArrow_condition R a)

def postnikovImageFactorisationArrowComparison : postnikovImageFactorisationArrowFunctor R n hn ⟶
    postnikovSourceImageArrowFunctor R n hn where
  app f := postnikovImageFactorisationComparison R f.hom.hom n hn
  naturality {_ _} a := postnikovImageFactorisationSquareMap_comparison R n hn _ _
    a.left.hom a.right.hom (postnikovSourceImageArrow_condition R a)

lemma postnikovImageFactorisationArrow_fac : postnikovImageFactorisationArrowSource R n hn ≫
    postnikovImageFactorisationArrowTarget R n hn =
      CategoryTheory.Functor.whiskerRight
        (Arrow.leftToRight : (Arrow.leftFunc : Arrow (NonpositiveAlgebra R) ⥤
        NonpositiveAlgebra R) ⟶ Arrow.rightFunc) (postnikovFunctor R (n + 1)) := by
  apply NatTrans.ext
  funext f
  exact postnikovImageFactorisation_fac R f.hom.hom n hn

lemma postnikovImageFactorisationArrowSource_comparison :
    postnikovImageFactorisationArrowSource R n hn ≫
      postnikovImageFactorisationArrowComparison R n hn =
      postnikovSourceImageArrowSource R n hn := by
  apply NatTrans.ext
  funext f
  exact postnikovImageFactorisationSource_comparison R f.hom.hom n hn

lemma postnikovImageFactorisationArrowComparison_quasiIso (f : Arrow (NonpositiveAlgebra R)) :
    QuasiIso ((postnikovImageFactorisationArrowComparison R n hn).app f).hom :=
  postnikovImageFactorisationComparison_quasiIso R f.hom.hom n hn

lemma postnikovImageFactorisationArrowSource_connected (f : Arrow (NonpositiveAlgebra R)) :
    IsConnected R ((postnikovImageFactorisationArrowSource R n hn).app f) (n + 1) :=
  postnikovImageFactorisationSource_connected_succ R f.hom.hom n hn

lemma postnikovImageFactorisationArrowObject_isConnective (f : Arrow (NonpositiveAlgebra R)) :
    IsConnective R ((postnikovImageFactorisationArrowFunctor R n hn).obj f) :=
  postnikovImageFactorisationObject_isConnective R f.hom.hom n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
