module

public import SerrePositivity.BhattScholze.DeltaRootSourceIteratedCompletionComplete
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul

/-! # 具体的根添加候補の正則生成元冪商とp導来完備性

A/(dⁿ)への実導来基底変更を、元のAへ係数制限して扱う。
商環上の完備性との係数環比較や離散性は別工程である。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b

/-- 正則dの実冪商への基底変更を制限すると、候補の実dⁿ Koszul錐になる。 -/
def deltaRootSourceGeneratorPowerReductionKoszulIso (hd : IsSMulRegular A d) (n : ℕ) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj ≅
        (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).obj (X₀).obj :=
  restrictedDerivedQuotientKoszulIso (d ^ n) (hd.pow n) X₀

/-- 正則dの任意冪商での実導来還元をAへ制限した対象は、p導来完備。 -/
theorem deltaRootSourceGeneratorPowerReduction_isComplete_p
    (hd : IsSMulRegular A d) (n : ℕ) :
    DerivedCompletion.IsComplete A (p : A)
      (((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj) := by
  let K := DerivedCategory.Q.objPreimage (X₀).obj
  let eK : DerivedCategory.Q.obj K ≅ (X₀).obj := DerivedCategory.Q.objObjPreimageIso (X₀).obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm
      (deltaRootSourceIteratedPDCompletion_isComplete_p D d b)
  have hC := DerivedCompletion.isComplete_Q_mappingCone A (p : A) (smulId (d ^ n) K) hK hK
  let e := deltaRootSourceGeneratorPowerReductionKoszulIso D d b hd n ≪≫
    (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).mapIso eK.symm ≪≫
      (DerivedCompletion.derivedScalarConeComparison A (d ^ n)).app K
  exact DerivedCompletion.isComplete_of_iso A (p : A) e.symm hC

local notation "Y₀" =>
  CategoryTheory.Functor.obj (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A))
    (DeltaRootSourceCoefficientObject d D b)
local notation "U₀" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- 最後のd完備化単位は、各生成元冪商での実還元後に同型になる。 -/
theorem deltaRootSourceGeneratorPowerReduction_unit_isIso
    (hd : IsSMulRegular A d) (n : ℕ) :
    IsIso ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).map
      ((U₀).app Y₀)) :=
  DerivedCompletion.boundedAboveDerivedCompletion_quotient_unit_isIso A d hd n Y₀

/-- p完備化済み対象と逐次対象の冪商還元を、標準d完備化単位で比較する。 -/
def deltaRootSourceGeneratorPowerReductionCompletionIso
    (hd : IsSMulRegular A d) (n : ℕ) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj Y₀ ≅
      (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀ := by
  have := deltaRootSourceGeneratorPowerReduction_unit_isIso D d b hd n
  exact asIso ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).map
    ((U₀).app Y₀))

/-- 冪商還元の比較逆射は、還元した標準d完備化単位の左逆である。 -/
theorem deltaRootSourceGeneratorPowerReductionCompletionIso_unit
    (hd : IsSMulRegular A d) (n : ℕ) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).map
        ((U₀).app Y₀) ≫
      (deltaRootSourceGeneratorPowerReductionCompletionIso D d b hd n).inv = 𝟙 _ :=
  (deltaRootSourceGeneratorPowerReductionCompletionIso D d b hd n).hom_inv_id

/-- 冪商の完備化比較は、実Koszul比較の下で標準単位の錐上の射に一致する。 -/
theorem deltaRootSourceGeneratorPowerReductionCompletionIso_koszul
    (hd : IsSMulRegular A d) (n : ℕ) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).map
        (deltaRootSourceGeneratorPowerReductionCompletionIso D d b hd n).hom).hom ≫
      (deltaRootSourceGeneratorPowerReductionKoszulIso D d b hd n).hom =
    (restrictedDerivedQuotientKoszulIso (d ^ n) (hd.pow n) Y₀).hom ≫
      (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).map (((U₀).app Y₀).hom) :=
  restrictedDerivedQuotientKoszulIso_naturality (d ^ n) (hd.pow n) ((U₀).app Y₀)

end SerrePositivity.BhattScholze
