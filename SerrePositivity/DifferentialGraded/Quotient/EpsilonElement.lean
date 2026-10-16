module
public import SerrePositivity.DifferentialGraded.Quotient.Differential
public import SerrePositivity.DifferentialGraded.Quotient.ErasureMiddleInterchange
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation
public import SerrePositivity.DifferentialGraded.Category.Components
public import SerrePositivity.DifferentialGraded.Complexes.UnitSandwichEvaluation

/-! # 商の指定次数−1生成元と単一pathの成分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma epsilonTerm_generator {S : Set D} (b : S) :
    (epsilonTerm A D b).f (-1)
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
    ιTensorObj (homObject A D b.val b.val)
      (epsilonComplex A ⊗ homObject A D b.val b.val) 0 (-1) (-1) (by omega)
      ((unitElement A b.val).val ⊗ₜ[A]
        ιTensorObj (epsilonComplex A) (homObject A D b.val b.val) (-1) 0 (-1) (by omega)
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A]
            (unitElement A b.val).val)) := by
  exact unitSandwich_apply (homObject A D b.val b.val) (epsilonComplex A)
    (eId (Complex A) b.val) (-1)
    ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))

variable [Small.{u} D]
/-- 指定対象の次数−1のpath生成元。最終微分について閉じているとは主張しない。 -/
def epsilonElement (S : Set D) (b : S) : (quotientHom A D S b.val b.val).X (-1) :=
  (epsilon A D S b).f (-1)
    ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))

end SerrePositivity.DifferentialGraded.DGQuotient
