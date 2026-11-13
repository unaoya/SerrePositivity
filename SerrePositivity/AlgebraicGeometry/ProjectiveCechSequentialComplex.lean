module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntLiftNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredComplex
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：有限被覆の実際の整数係数 Čech 複体と自然数の順極限を比較する。
方針：係数環を ULift ℤ へ移送し、有限な各項の既存の比較を使う。
規約：加群の宇宙を自然数や整数の宇宙に制限しない。
使われ方：Frobenius 後の細分写像を、各段の細分写像の余極限と照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {ι : Type} [DecidableEq ι]

/-- 整数係数の複体と、ULift ℤ に移して戻した複体の自然同型。 -/
def projectiveIntCechLiftComplexNatIso :
    fullCechComplexFunctor (R := ℤ) (ι := ι) ≅
      projectiveIntCechLiftFunctor.{u} ⋙ fullCechComplexFunctor ⋙
        (ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ))).mapHomologicalComplex
          (.up ℕ) :=
  NatIso.ofComponents (fun D ↦
    fullCechComplexFunctor.mapIso (projectiveIntCechLiftRoundtripIso D).symm ≪≫
      projectiveCechIntRestrictionComplexIso (projectiveIntCechLiftDiagram D)) (by
        intro D E η
        ext q x
        rfl)

variable [Fintype ι]

/-- 有限被覆の整数係数 Čech 複体は任意の宇宙で自然数順極限を保つ。 -/
instance projectiveIntFullCechFunctorPreservesSequentialColimits :
    PreservesColimitsOfShape ℕ
      (fullCechComplexFunctor : (Finset ι ⥤ ModuleCat.{u} ℤ) ⥤
        CochainComplex (ModuleCat.{u} ℤ) ℕ) := by
  haveI : PreservesColimitsOfShape ℕ
      (fullCechComplexFunctor : (Finset ι ⥤ ModuleCat.{u} (ULift.{u} ℤ)) ⥤
        CochainComplex (ModuleCat.{u} (ULift.{u} ℤ)) ℕ) :=
    preservesColimitsOfShape_of_equiv (AsSmall.equiv.symm : AsSmall.{u} ℕ ≌ ℕ) _
  exact preservesColimitsOfShape_of_natIso (projectiveIntCechLiftComplexNatIso.{u}).symm

/-- 係数の自然数順極限の Čech 複体と、各段の複体の順極限との標準同型。 -/
def projectiveIntCechSequentialComplexIso (D : ℕ ⥤ Finset ι ⥤ ModuleCat.{u} ℤ) :
    fullCechComplex (colimit D) ≅ colimit (D ⋙ fullCechComplexFunctor) :=
  preservesColimitIso (fullCechComplexFunctor (R := ℤ) (ι := ι)) D

end SerrePositivity.AlgebraicGeometry
