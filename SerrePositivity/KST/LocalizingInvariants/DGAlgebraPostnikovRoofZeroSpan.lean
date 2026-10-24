module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLeg
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveNativeInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.ProInverseEventualUniqueness

/-!
概要：任意の有限段の実逆 roof から、同じ脚と厳密左三角形を持つ零底の逆を回収する。
方針：元の分母・分子・左細分を同じ零切断へ降ろし、可逆な両分母を消去する。
規約：一切断に限定せず元の細分を保持。使われ方：高次段の係数逆の共通底。
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

local instance apex_nonpositive : c.roof.apex.X.IsStrictlyLE 0 := c.roof_nonpositive
local instance source_nonpositive : c.source.X.IsStrictlyLE 0 := c.source_nonpositive

def denominator : postnikov R c.roof.apex 0 ⟶ postnikov R (B.obj m).obj 0 :=
  postnikovZeroLeg R n hn (B.obj m) c.roof.denominator

def numerator : postnikov R c.roof.apex 0 ⟶ postnikov R (A.obj i).obj 0 :=
  postnikovZeroLeg R n hn (A.obj i) c.roof.numerator

def sourceProjection : postnikov R c.source 0 ⟶ postnikov R (A.obj m).obj 0 :=
  postnikovZeroLeg R n hn (A.obj m) c.sourceProjection

lemma denominator_isIso : IsIso (denominator R n hn f c) :=
  postnikovZeroLeg_isIso R n hn (B.obj m) c.roof.denominator c.roof.denominator_quasiIso

lemma sourceProjection_isIso : IsIso (sourceProjection R n hn f c) :=
  postnikovZeroLeg_isIso R n hn (A.obj m) c.sourceProjection c.sourceProjection_quasiIso

lemma source_denominator : postnikovMap R c.sourceLift 0 ≫ denominator R n hn f c =
    sourceProjection R n hn f c ≫ postnikovMap R (f.app m).hom 0 :=
  postnikovZeroLeg_square R n hn (B.obj m) (A.obj m) c.roof.denominator
    c.sourceLift c.sourceProjection (f.app m) c.source_denominator

lemma source_numerator : postnikovMap R c.sourceLift 0 ≫ numerator R n hn f c =
    sourceProjection R n hn f c ≫ postnikovMap R (A.transition hi).hom 0 :=
  postnikovZeroLeg_square R n hn (A.obj i) (A.obj m) c.roof.numerator
    c.sourceLift c.sourceProjection (A.transition hi) c.source_numerator

def inverse : postnikov R (B.obj m).obj 0 ⟶ postnikov R (A.obj i).obj 0 := by
  have := denominator_isIso R n hn f c
  exact inv (denominator R n hn f c) ≫ numerator R n hn f c

lemma denominator_inverse : denominator R n hn f c ≫ inverse R n hn f c = numerator R n hn f c := by
  have := denominator_isIso R n hn f c
  exact IsIso.hom_inv_id_assoc _ _

lemma inverse_left : postnikovMap R (f.app m).hom 0 ≫ inverse R n hn f c =
    postnikovMap R (A.transition hi).hom 0 := by
  have := denominator_isIso R n hn f c
  have := sourceProjection_isIso R n hn f c
  exact TowerDiagram.inverse_span_left (sourceProjection R n hn f c)
    (postnikovMap R c.sourceLift 0) (denominator R n hn f c) (numerator R n hn f c) _ _
    (source_denominator R n hn f c) (source_numerator R n hn f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovRoofZeroSpan
