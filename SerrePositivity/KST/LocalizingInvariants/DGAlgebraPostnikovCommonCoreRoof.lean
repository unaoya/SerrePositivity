module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreLayerInverse
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreShifted

/-!
概要：Common 系の一般化で使う、非負切断次数付きの下段 roof 界面。
方針：次数とその非負性を下段に保持し、既存の共通核の実射を公開する。
規約：単位 shift は切断次数に含めない。使われ方：旧 n=1 界面を保つ段階的移行。
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

abbrev lowerFunctor (R : Type u) [CommRing R] (n : ℤ) (_hn : 0 ≤ n) :=
  postnikovFunctor R n

variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

abbrev PostnikovCommonLayerInverse := LayerInverse R hn f c

abbrev roofRefine {k : ℕ} (hm : m ≤ k) := c.refine R hm

abbrev roofNumeratorLayer := numeratorLayer R hn f c
abbrev roofDenominatorLayer := denominatorLayer R hn f c
abbrev roofShiftedNumeratorLayer (s : ℤ) := shiftedNumeratorLayer R hn f c s
abbrev roofShiftedDenominatorLayer (s : ℤ) := shiftedDenominatorLayer R hn f c s

local instance roof_apex_nonpositive : c.roof.apex.X.IsStrictlyLE 0 := c.roof_nonpositive

abbrev roofZeroBase := postnikov R c.roof.apex 0
abbrev roofZeroDenominator := PostnikovRoofZeroSpan.denominator R n hn f c
abbrev roofZeroNumerator := PostnikovRoofZeroSpan.numerator R n hn f c

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
