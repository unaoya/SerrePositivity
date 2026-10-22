module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerInverseComponents
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionOver

/-!
概要：作用を保つ元の係数逆を、後続段の元の層遷移で前合成する。
方針：実双加群射の底を変える合成を使い、元の両 cochain 三角形を保持する。
規約：元の底・係数の逆を取り替えない。使われ方：共通零底上の実係数逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovZeroLayerInverse
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {A B : Tower (NonpositiveAlgebra R)}
  {f : LevelHom A B} {i l : ℕ} {hj : i ≤ l}
  (e : PostnikovZeroLayerInverse R n f i l hj) {k : ℕ} (hl : l ≤ k)

def refinedCoefficient : postnikovLayerZeroBimodule R (B.obj k).obj n ⟶
    bimoduleRestrict (postnikovMap R (B.transition hl).hom 0 ≫ e.base)
      (postnikovLayerZeroBimodule R (A.obj i).obj n) :=
  bimoduleMapOverComp (postnikovMap R (B.transition hl).hom 0) e.base e.coefficient
    (postnikovLayerZeroMap R (B.transition hl).hom n)

lemma refinedCoefficient_hom : (refinedCoefficient R e hl).hom =
    postnikovLayerMap R (B.transition hl).hom n ≫ e.coefficient.hom :=
  bimoduleMapOverComp_hom _ _ _ _

lemma refinedCoefficient_left : postnikovLayerMap R (f.app k).hom n ≫
    (refinedCoefficient R e hl).hom = postnikovLayerMap R (A.transition (hj.trans hl)).hom n := by
  have hnat : postnikovLayerMap R (A.transition hl).hom n ≫
      postnikovLayerMap R (f.app l).hom n = postnikovLayerMap R (f.app k).hom n ≫
        postnikovLayerMap R (B.transition hl).hom n :=
    (f.map (postnikovLayerFunctor R n)).naturality hl
  change postnikovLayerMap R (f.app k).hom n ≫
    (postnikovLayerMap R (B.transition hl).hom n ≫ e.coefficient.hom) = _
  calc
    _ = (postnikovLayerMap R (A.transition hl).hom n ≫
        postnikovLayerMap R (f.app l).hom n) ≫ e.coefficient.hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ e.coefficient.hom) hnat.symm)
    _ = postnikovLayerMap R (A.transition hl).hom n ≫
        postnikovLayerMap R (A.transition hj).hom n :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => postnikovLayerMap R (A.transition hl).hom n ≫ t) e.left_coefficient)
    _ = postnikovLayerMap R ((A.transition hl).hom ≫ (A.transition hj).hom) n :=
      (postnikovLayerMap_comp R n _ _).symm
    _ = _ := congrArg (fun t => postnikovLayerMap R t n)
      (congrArg (fun t => t.hom) (A.transition_comp hl hj))

lemma refinedCoefficient_right : (refinedCoefficient R e hl).hom ≫
    postnikovLayerMap R (f.app i).hom n =
      postnikovLayerMap R (B.transition (hj.trans hl)).hom n := by
  change (postnikovLayerMap R (B.transition hl).hom n ≫ e.coefficient.hom) ≫
    postnikovLayerMap R (f.app i).hom n = _
  calc
    _ = postnikovLayerMap R (B.transition hl).hom n ≫
        postnikovLayerMap R (B.transition hj).hom n :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => postnikovLayerMap R (B.transition hl).hom n ≫ t) e.right_coefficient)
    _ = postnikovLayerMap R ((B.transition hl).hom ≫ (B.transition hj).hom) n :=
      (postnikovLayerMap_comp R n _ _).symm
    _ = _ := congrArg (fun t => postnikovLayerMap R t n)
      (congrArg (fun t => t.hom) (B.transition_comp hl hj))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovZeroLayerInverse
