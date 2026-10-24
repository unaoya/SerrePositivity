module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofZeroRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerInverseRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroPro

/-!
概要：切断次数と層次数を独立にして、共通零底と係数逆を構成する。
方針：零底の逆の eventual 一意性と、同じ係数の実制限を使う。
規約：切断次数は下段 roof から推論し、層次数を別引数にする。
使われ方：既存の一切断 roof 上の任意層 API と、共通核の同次数の場合の特殊化。
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
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n) (ℓ : ℤ)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)

attribute [local instance] PostnikovRoofZeroSpan.original_apex_nonpositive
  PostnikovRoofZeroSpan.refined_sourceLevel_nonpositive
  PostnikovRoofZeroSpan.refined_targetLevel_nonpositive
  PostnikovRoofZeroSpan.refined_apex_nonpositive

abbrev zeroDenominatorLayerAt :=
  bimoduleRestrict (PostnikovRoofZeroSpan.denominator R n hn f c)
    (postnikovLayerZeroBimodule R (B.obj m).obj ℓ)

abbrev zeroNumeratorLayerAt :=
  bimoduleRestrict (PostnikovRoofZeroSpan.numerator R n hn f c)
    (postnikovLayerZeroBimodule R (A.obj i).obj ℓ)

variable {l : ℕ} {hj : i ≤ l} (e : PostnikovZeroLayerInverse R ℓ f i l hj)

lemma zeroInverse_eventually_layerAt
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k,
      postnikovMap R (B.transition hm).hom 0 ≫ PostnikovRoofZeroSpan.inverse R n hn f c =
        postnikovMap R (B.transition hl).hom 0 ≫ e.base :=
  TowerDiagram.inverse_left_eventually_unique (f.map (postnikovFunctor R 0))
    (postnikovZeroMap_isProIso R f h₀) hi hj (PostnikovRoofZeroSpan.inverse R n hn f c) e.base
    (PostnikovRoofZeroSpan.inverse_left R n hn f c) e.left_base

lemma commonZeroBase_atLayer
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k,
      PostnikovRoofZeroSpan.numerator R n hn f (c.refine R hm) =
        PostnikovRoofZeroSpan.denominator R n hn f (c.refine R hm) ≫
          postnikovMap R (B.transition hl).hom 0 ≫ e.base := by
  obtain ⟨k, hm, hl, he⟩ := zeroInverse_eventually_layerAt R hn ℓ f c e h₀
  refine ⟨k, hm, hl, ?_⟩
  let p := postnikovMap R (c.refinementProjection R hm) 0
  have hd := PostnikovRoofZeroSpan.refinement_denominator_square R n hn f c hm
  have hnum := PostnikovRoofZeroSpan.refinement_numerator_square R n hn f c hm
  calc
    PostnikovRoofZeroSpan.numerator R n hn f (c.refine R hm) =
        p ≫ PostnikovRoofZeroSpan.numerator R n hn f c := hnum.symm
    _ = p ≫ (PostnikovRoofZeroSpan.denominator R n hn f c ≫
        PostnikovRoofZeroSpan.inverse R n hn f c) :=
      congrArg (fun t => p ≫ t) (PostnikovRoofZeroSpan.denominator_inverse R n hn f c).symm
    _ = (p ≫ PostnikovRoofZeroSpan.denominator R n hn f c) ≫
        PostnikovRoofZeroSpan.inverse R n hn f c := (Category.assoc _ _ _).symm
    _ = (PostnikovRoofZeroSpan.denominator R n hn f (c.refine R hm) ≫
        postnikovMap R (B.transition hm).hom 0) ≫ PostnikovRoofZeroSpan.inverse R n hn f c :=
      congrArg (fun t => t ≫ PostnikovRoofZeroSpan.inverse R n hn f c) hd
    _ = PostnikovRoofZeroSpan.denominator R n hn f (c.refine R hm) ≫
        (postnikovMap R (B.transition hl).hom 0 ≫ e.base) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => PostnikovRoofZeroSpan.denominator R n hn f (c.refine R hm) ≫ t) he)

variable {k : ℕ} (hm : m ≤ k) (hl : l ≤ k)
  (hb : PostnikovRoofZeroSpan.numerator R n hn f (c.refine R hm) =
    PostnikovRoofZeroSpan.denominator R n hn f (c.refine R hm) ≫
      postnikovMap R (B.transition hl).hom 0 ≫ e.base)

abbrev zeroCoefficientAt :
    zeroDenominatorLayerAt R hn ℓ f (c.refine R hm) ⟶
      zeroNumeratorLayerAt R hn ℓ f (c.refine R hm) :=
  bimoduleRestrictOver (PostnikovRoofZeroSpan.denominator R n hn f (c.refine R hm))
    (PostnikovRoofZeroSpan.numerator R n hn f (c.refine R hm))
    (postnikovMap R (B.transition hl).hom 0 ≫ e.base) hb.symm
    (PostnikovZeroLayerInverse.refinedCoefficient R e hl)

lemma zeroCoefficientAt_refined_hom : (zeroCoefficientAt R hn ℓ f c e hm hl hb).hom =
    (PostnikovZeroLayerInverse.refinedCoefficient R e hl).hom :=
  bimoduleRestrictOver_hom _ _ _ _ _

lemma zeroCoefficientAt_hom : (zeroCoefficientAt R hn ℓ f c e hm hl hb).hom =
    postnikovLayerMap R (B.transition hl).hom ℓ ≫ e.coefficient.hom :=
  (zeroCoefficientAt_refined_hom R hn ℓ f c e hm hl hb).trans
    (PostnikovZeroLayerInverse.refinedCoefficient_hom R e hl)

lemma zeroCoefficientAt_left : postnikovLayerMap R (f.app k).hom ℓ ≫
    (zeroCoefficientAt R hn ℓ f c e hm hl hb).hom =
      postnikovLayerMap R (A.transition (hj.trans hl)).hom ℓ :=
  (congrArg (fun t => postnikovLayerMap R (f.app k).hom ℓ ≫ t)
    (zeroCoefficientAt_refined_hom R hn ℓ f c e hm hl hb)).trans
      (PostnikovZeroLayerInverse.refinedCoefficient_left R e hl)

lemma zeroCoefficientAt_right : (zeroCoefficientAt R hn ℓ f c e hm hl hb).hom ≫
    postnikovLayerMap R (f.app i).hom ℓ =
      postnikovLayerMap R (B.transition (hj.trans hl)).hom ℓ :=
  (congrArg (fun t => t ≫ postnikovLayerMap R (f.app i).hom ℓ)
    (zeroCoefficientAt_refined_hom R hn ℓ f c e hm hl hb)).trans
      (PostnikovZeroLayerInverse.refinedCoefficient_right R e hl)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
