module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofZeroRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerInverseComponents
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroPro

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreZeroLayerAtCutoff

/-!
概要：任意の有限段の roof と元の層逆の零底を、後続の同じ細分上で厳密に揃える。
方針：元の零射の pro 逆の eventual 一意性を、元の細分の零脚正方形へ適用する。
規約：両逆を選び直さず層作用の底を保持。使われ方：高次係数の共通底への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovRoofZeroSpan
open ProExcision
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)
  (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
  {l : ℕ} {hj : i ≤ l} (e : PostnikovZeroLayerInverse R n f i l hj)

include h₀

lemma inverse_eventually_layerInverse :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k,
      postnikovMap R (B.transition hm).hom 0 ≫ inverse R n hn f c =
        postnikovMap R (B.transition hl).hom 0 ≫ e.base :=
  PostnikovCommonCore.zeroInverse_eventually_layerAt R hn n f c e h₀

local instance refined_source_nonpositive (k : ℕ) :
    ((A.map (postnikovFunctor R n)).obj k).X.IsStrictlyLE 0 := postnikov_nonpositive R _ n
local instance refined_target_nonpositive (k : ℕ) :
    ((B.map (postnikovFunctor R n)).obj k).X.IsStrictlyLE 0 := postnikov_nonpositive R _ n

attribute [local instance] original_apex_nonpositive refined_apex_nonpositive

lemma common_zero_base :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k,
      numerator R n hn f (c.refine R hm) =
        denominator R n hn f (c.refine R hm) ≫ postnikovMap R (B.transition hl).hom 0 ≫ e.base :=
  PostnikovCommonCore.commonZeroBase_atLayer R hn n f c e h₀

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovRoofZeroSpan
