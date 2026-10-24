module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofZeroRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerBaseNaturality
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionSquareMap
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionComposition

/-!
概要：任意の切断次数の下段 roof 上に、共通核の層と細分比較を構成する。
方針：下段 roof から切断次数を推論し、元の両脚に沿う層の制限を使う。
規約：切断次数 n と単位 shift 1 を区別する。使われ方：Common 系の共通核。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)

abbrev numeratorLayer : Bimod c.roof.apex c.roof.apex :=
  bimoduleRestrict c.roof.numerator (postnikovLayerBaseBimodule R (A.obj i).obj n hn)

abbrev denominatorLayer : Bimod c.roof.apex c.roof.apex :=
  bimoduleRestrict c.roof.denominator (postnikovLayerBaseBimodule R (B.obj m).obj n hn)

attribute [local instance] PostnikovRoofZeroSpan.refined_sourceLevel_nonpositive
  PostnikovRoofZeroSpan.refined_targetLevel_nonpositive

variable {k : ℕ} (hm : m ≤ k)

abbrev refineNumeratorLayerIso :
    numeratorLayer R hn f (c.refine R hm) ≅
      bimoduleRestrict (c.refinementProjection R hm)
        (numeratorLayer R hn f c) :=
  bimoduleRestrictionCompIso (c.refinementProjection R hm) c.roof.numerator
    (postnikovLayerBaseBimodule R (A.obj i).obj n hn)

lemma refineNumeratorLayerIso_hom :
    (refineNumeratorLayerIso R hn f c hm).hom.hom =
      𝟙 (postnikovLayer R (A.obj i).obj n) := rfl

abbrev refineDenominatorLayerMap :
    denominatorLayer R hn f (c.refine R hm) ⟶
      bimoduleRestrict (c.refinementProjection R hm)
        (denominatorLayer R hn f c) :=
  bimoduleRestrictSquareMap (c.refine R hm).roof.denominator
    c.roof.denominator (c.refinementProjection R hm)
    (postnikovMap R (B.transition hm).hom n)
    (c.refinementProjection_denominator R hm).symm
    (postnikovLayerBaseMap R (B.transition hm).hom n hn)

lemma refineDenominatorLayerMap_hom :
    (refineDenominatorLayerMap R hn f c hm).hom =
      postnikovLayerMap R (B.transition hm).hom n := rfl

lemma numeratorLayer_lowerBound :
    (numeratorLayer R hn f c).X.IsStrictlyGE (-(n + 1)) :=
  postnikovLayer_lowerBound R (A.obj i).obj n

lemma numeratorLayer_upperBound :
    (numeratorLayer R hn f c).X.IsStrictlyLE (-(n + 1)) :=
  postnikovLayer_upperBound R (A.obj i).obj n

lemma denominatorLayer_lowerBound :
    (denominatorLayer R hn f c).X.IsStrictlyGE (-(n + 1)) :=
  postnikovLayer_lowerBound R (B.obj m).obj n

lemma denominatorLayer_upperBound :
    (denominatorLayer R hn f c).X.IsStrictlyLE (-(n + 1)) :=
  postnikovLayer_upperBound R (B.obj m).obj n

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
