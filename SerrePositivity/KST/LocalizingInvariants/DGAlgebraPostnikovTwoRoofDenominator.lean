module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneNonpositiveInverseRoof

/-!
概要：元の一切断逆の分母に沿う、元の二切断拡大の実底変更を供給する。
方針：元の非正次数の実 roof を用い、上段への準同型比較・元の kernel と層を保持。
規約：分子側と π₂ 層の逆の貼合せは未提供。使われ方：LT の高次有限切断比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

def postnikovTwoRoofDenominator : Mon (Complex R) :=
  postnikovRoofBaseChange R (B.obj m).obj 1 c.roof

def postnikovTwoRoofDenominatorUpper :
    postnikovTwoRoofDenominator R f c ⟶ postnikov R (B.obj m).obj 2 :=
  postnikovExtensionBaseChangeUpper R (B.obj m).obj 1 c.roof.denominator

def postnikovTwoRoofDenominatorBase : postnikovTwoRoofDenominator R f c ⟶ c.roof.apex :=
  postnikovExtensionBaseChangeBase R (B.obj m).obj 1 c.roof.denominator

lemma postnikovTwoRoofDenominator_nonpositive :
    (postnikovTwoRoofDenominator R f c).X.IsStrictlyLE 0 :=
  postnikovRoofBaseChange_nonpositive R (B.obj m).obj 1 c.roof c.roof_nonpositive

lemma postnikovTwoRoofDenominatorUpper_epi : Epi (postnikovTwoRoofDenominatorUpper R f c).hom :=
  (postnikovRoofBaseChangeUpperInverse R (B.obj m).obj 1 c.roof).denominator_epi

lemma postnikovTwoRoofDenominatorUpper_quasiIso :
    QuasiIso (postnikovTwoRoofDenominatorUpper R f c).hom :=
  (postnikovRoofBaseChangeUpperInverse R (B.obj m).obj 1 c.roof).denominator_quasiIso

lemma postnikovTwoRoofDenominatorBase_connected :
    IsConnected R (postnikovTwoRoofDenominatorBase R f c) 2 :=
  postnikovRoofBaseChangeBase_connected R (B.obj m).obj 1 c.roof

def postnikovTwoRoofDenominatorKernelHomologyIso :
    (kernel (postnikovTwoRoofDenominatorBase R f c).hom).homology (-2) ≅
      (B.obj m).obj.X.homology (-2) :=
  postnikovBaseChangedKernelHomologyIso R (B.obj m).obj 1 c.roof.denominator

lemma exists_postnikovTwoRoofDenominator
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
    ∃ c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi,
      (postnikovTwoRoofDenominator R f c).X.IsStrictlyLE 0 ∧
        Epi (postnikovTwoRoofDenominatorUpper R f c).hom ∧
        QuasiIso (postnikovTwoRoofDenominatorUpper R f c).hom ∧
        IsConnected R (postnikovTwoRoofDenominatorBase R f c) 2 := by
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovOneMap_exists_nonpositiveInverseRoof R f h₀ h₁ i
  exact ⟨m, hi, c, postnikovTwoRoofDenominator_nonpositive R f c,
    postnikovTwoRoofDenominatorUpper_epi R f c, postnikovTwoRoofDenominatorUpper_quasiIso R f c,
    postnikovTwoRoofDenominatorBase_connected R f c⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
