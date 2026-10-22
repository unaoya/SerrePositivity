module

public import SerrePositivity.KST.LocalizingInvariants.CochainSplitKernel
public import SerrePositivity.KST.LocalizingInvariants.CochainConeQuotientComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
概要：負の直和第一包含の mapping cocone は、第二成分の負一 shift と準同型である。
方針：元の商射への cone 準同型比較を shift し、元のホモロジー同型を回収する。
規約：元の負符号と商射を保持。使われ方：平方零拡大の fiber 係数の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] (P T : Complex R)

def cochainNegInlCoconeComparison : mappingCocone (-(biprod.inl : P ⟶ P ⊞ T)) ⟶ T⟦(-1 : ℤ)⟧ :=
  (cochainConeQuotient (-(biprod.inl : P ⟶ P ⊞ T)) (biprod.snd : P ⊞ T ⟶ T) (by simp))⟦-1⟧'

lemma cochainNegInlCoconeComparison_quasiIso : QuasiIso (cochainNegInlCoconeComparison P T) := by
  have := cochainBiprodNegInlKernelLift_isIso P T
  have hc : QuasiIso (cochainConeQuotient (-(biprod.inl : P ⟶ P ⊞ T))
      (biprod.snd : P ⊞ T ⟶ T) (by simp)) := by
    apply cochainConeQuotient_quasiIso
    exact quasiIso_of_isIso _
  change QuasiIso ((cochainConeQuotient (-(biprod.inl : P ⟶ P ⊞ T))
    (biprod.snd : P ⊞ T ⟶ T) (by simp))⟦(-1 : ℤ)⟧')
  infer_instance

def cochainNegInlCoconeHomologyIso (j : ℤ) :
    (mappingCocone (-(biprod.inl : P ⟶ P ⊞ T))).homology j ≅ T.homology (j - 1) := by
  have := cochainNegInlCoconeComparison_quasiIso P T
  exact asIso (homologyMap (cochainNegInlCoconeComparison P T) j) ≪≫
    (((homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso (-1) j (j - 1) (by omega)).app T)

end SerrePositivity.KST.LocalizingInvariants
