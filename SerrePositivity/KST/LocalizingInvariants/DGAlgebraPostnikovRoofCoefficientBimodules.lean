module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneRoofRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerBaseNaturality
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionSquareMap
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionComposition

/-!
概要：細分 roof の共通底上に元の二つの層双加群を置き、元の遷移を作用保存射にする。
方針：実分子・分母に沿って制限し、元の厳密な底正方形を既存の層自然性へ渡す。
規約：R 線形逆の作用保存は仮定しない。使われ方：係数逆の双加群整合の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

def postnikovOneRoofNumeratorLayer : Bimod c.roof.apex c.roof.apex :=
  bimoduleRestrict c.roof.numerator (postnikovLayerBaseBimodule R (A.obj i).obj 1 (by omega))

def postnikovOneRoofDenominatorLayer : Bimod c.roof.apex c.roof.apex :=
  bimoduleRestrict c.roof.denominator (postnikovLayerBaseBimodule R (B.obj m).obj 1 (by omega))

variable {k : ℕ} (hm : m ≤ k)

def postnikovOneRoofRefineNumeratorLayerIso :
    postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c hm) ≅
      bimoduleRestrict (postnikovOneRoofRefineProjection R f c hm)
        (postnikovOneRoofNumeratorLayer R f c) :=
  bimoduleRestrictionCompIso (postnikovOneRoofRefineProjection R f c hm) c.roof.numerator
    (postnikovLayerBaseBimodule R (A.obj i).obj 1 (by omega))

lemma postnikovOneRoofRefineNumeratorLayerIso_hom :
    (postnikovOneRoofRefineNumeratorLayerIso R f c hm).hom.hom =
      𝟙 (postnikovLayer R (A.obj i).obj 1) := rfl

def postnikovOneRoofRefineDenominatorLayerMap :
    postnikovOneRoofDenominatorLayer R f (postnikovOneRoofRefine R f c hm) ⟶
      bimoduleRestrict (postnikovOneRoofRefineProjection R f c hm)
        (postnikovOneRoofDenominatorLayer R f c) :=
  bimoduleRestrictSquareMap (postnikovOneRoofRefine R f c hm).roof.denominator
    c.roof.denominator (postnikovOneRoofRefineProjection R f c hm)
    (postnikovMap R (B.transition hm).hom 1)
    (postnikovOneRoofRefineProjection_denominator R f c hm).symm
    (postnikovLayerBaseMap R (B.transition hm).hom 1 (by omega))

lemma postnikovOneRoofRefineDenominatorLayerMap_hom :
    (postnikovOneRoofRefineDenominatorLayerMap R f c hm).hom =
      postnikovLayerMap R (B.transition hm).hom 1 := rfl

lemma postnikovOneRoofNumeratorLayer_lowerBound :
    (postnikovOneRoofNumeratorLayer R f c).X.IsStrictlyGE (-2) :=
  postnikovLayer_lowerBound R (A.obj i).obj 1

lemma postnikovOneRoofNumeratorLayer_upperBound :
    (postnikovOneRoofNumeratorLayer R f c).X.IsStrictlyLE (-2) :=
  postnikovLayer_upperBound R (A.obj i).obj 1

lemma postnikovOneRoofDenominatorLayer_lowerBound :
    (postnikovOneRoofDenominatorLayer R f c).X.IsStrictlyGE (-2) :=
  postnikovLayer_lowerBound R (B.obj m).obj 1

lemma postnikovOneRoofDenominatorLayer_upperBound :
    (postnikovOneRoofDenominatorLayer R f c).X.IsStrictlyLE (-2) :=
  postnikovLayer_upperBound R (B.obj m).obj 1

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
