module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraZeroDescIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneRoofRefinement

/-!
概要：元の一切断逆 roof の零切断を、実可逆分母と元の分子を持つ代数 span にする。
方針：元の両脚を元の零切断への遷移と合成し、同じ頂点の零切断から降ろす。
規約：二重切断の任意同型を選ばない。使われ方：作用を保つ係数逆との底の一致。
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

local instance oneRoofZero_apex_nonpositive : c.roof.apex.X.IsStrictlyLE 0 := c.roof_nonpositive
local instance oneRoofZero_targetA_lowerBound : (postnikov R (A.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (A.obj i).obj 0
local instance oneRoofZero_targetB_lowerBound : (postnikov R (B.obj m).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj m).obj 0
local instance oneRoofZero_targetB_nonpositive : (postnikov R (B.obj m).obj 0).X.IsStrictlyLE 0 :=
  postnikovComplex_nonpositive R (B.obj m).obj 0

@[reducible]
def postnikovOneRoofZeroBase : Mon (Complex R) := postnikov R c.roof.apex 0

@[reducible]
def postnikovOneRoofZeroDenominator : postnikovOneRoofZeroBase R f c ⟶
    postnikov R (B.obj m).obj 0 :=
  postnikovDesc R 0 (c.roof.denominator ≫ postnikovTransition R (B.obj m).obj 1 0 (by omega))

@[reducible]
def postnikovOneRoofZeroNumerator : postnikovOneRoofZeroBase R f c ⟶
    postnikov R (A.obj i).obj 0 :=
  postnikovDesc R 0 (c.roof.numerator ≫ postnikovTransition R (A.obj i).obj 1 0 (by omega))

lemma postnikovOneRoofZeroDenominator_projection : postnikovQuotient R c.roof.apex 0 ≫
    postnikovOneRoofZeroDenominator R f c =
      c.roof.denominator ≫ postnikovTransition R (B.obj m).obj 1 0 (by omega) :=
  postnikovQuotient_desc R 0 _

lemma postnikovOneRoofZeroNumerator_projection : postnikovQuotient R c.roof.apex 0 ≫
    postnikovOneRoofZeroNumerator R f c =
      c.roof.numerator ≫ postnikovTransition R (A.obj i).obj 1 0 (by omega) :=
  postnikovQuotient_desc R 0 _

lemma postnikovOneRoofZeroDenominator_isIso : IsIso (postnikovOneRoofZeroDenominator R f c) := by
  have hd := groups_map_isIso_of_quasiIso R c.roof.denominator c.roof.denominator_quasiIso 0
  have ht := groups_map_isIso_of_quasiIsoAt R
    (postnikovTransition R (B.obj m).obj 1 0 (by omega)) 0
    (postnikovTransition_quasiIsoAt R (B.obj m).obj 1 0 (by omega) 0 (by omega))
  apply postnikovDesc_zero_isIso_of_groups R
  rw [Functor.map_comp]
  infer_instance

@[reducible]
def postnikovOneRoofZeroInverse : postnikov R (B.obj m).obj 0 ⟶ postnikov R (A.obj i).obj 0 := by
  have := postnikovOneRoofZeroDenominator_isIso R f c
  exact inv (postnikovOneRoofZeroDenominator R f c) ≫ postnikovOneRoofZeroNumerator R f c

lemma postnikovOneRoofZeroInverse_denominator : postnikovOneRoofZeroDenominator R f c ≫
    postnikovOneRoofZeroInverse R f c = postnikovOneRoofZeroNumerator R f c := by
  have := postnikovOneRoofZeroDenominator_isIso R f c
  change postnikovOneRoofZeroDenominator R f c ≫
    (inv (postnikovOneRoofZeroDenominator R f c) ≫ postnikovOneRoofZeroNumerator R f c) = _
  exact IsIso.hom_inv_id_assoc _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
