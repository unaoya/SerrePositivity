module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageTargetSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisation

/-!
概要：元の標的上段までの像因子分解の中間代数を、矢印圏上の厳密な実関手にする。
方針：源側像拡大と標的 class 模型・元の標的上段の cospan を作り、実模型関手に合成。
規約：元の対象・元の二つの cospan 射を保持。使われ方：LT の実因子分解の図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)

def postnikovSourceImageToTargetNat : postnikovSourceImageArrowFunctor R n hn ⟶
    (Arrow.rightFunc : Arrow (NonpositiveAlgebra R) ⥤ NonpositiveAlgebra R) ⋙
      postnikovClassModelFunctor R n hn where
  app f := postnikovSourceImageToTarget R f.hom.hom n hn
  naturality {_ _} a := (postnikovSourceImageToTarget_square R n hn _ _ a.left.hom a.right.hom
    (postnikovSourceImageArrow_condition R a)).symm

def postnikovImageFactorisationCospanFunctor :
    Arrow (NonpositiveAlgebra R) ⥤ (WalkingCospan ⥤ Mon (Complex R)) where
  obj f := cospan (postnikovSourceImageToTarget R f.hom.hom n hn)
    (postnikovHomotopyPullbackComparison R f.right.obj n hn)
  map a := cospanHomMk ((postnikovClassModelFunctor R n hn).map a.right)
    ((postnikovSourceImageArrowFunctor R n hn).map a) ((postnikovFunctor R (n + 1)).map a.right)
    (postnikovSourceImageToTarget_square R n hn _ _ a.left.hom a.right.hom
      (postnikovSourceImageArrow_condition R a))
    (postnikovHomotopyPullbackComparison_square R n hn a.right.hom).symm
  map_id f := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact (postnikovClassModelFunctor R n hn).map_id f.right
    · exact (postnikovSourceImageArrowFunctor R n hn).map_id f
    · exact (postnikovFunctor R (n + 1)).map_id f.right
  map_comp a b := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact (postnikovClassModelFunctor R n hn).map_comp a.right b.right
    · exact (postnikovSourceImageArrowFunctor R n hn).map_comp a b
    · exact (postnikovFunctor R (n + 1)).map_comp a.right b.right

def postnikovImageFactorisationArrowFunctor : Arrow (NonpositiveAlgebra R) ⥤ Mon (Complex R) :=
  postnikovImageFactorisationCospanFunctor R n hn ⋙ HomotopyPullbackModel.diagramFunctor R

lemma postnikovImageFactorisationArrowFunctor_obj (f : Arrow (NonpositiveAlgebra R)) :
    (postnikovImageFactorisationArrowFunctor R n hn).obj f =
      postnikovImageFactorisationObject R f.hom.hom n hn := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
