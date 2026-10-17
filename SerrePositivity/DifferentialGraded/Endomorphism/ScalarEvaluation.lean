module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedScalarTensor
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedEvaluation

/-! # balanced合成評価の係数変更と導来比較射の可換性

係数変更したHom因子をそのまま保持する。実際の係数変更先のHomとの同型性は主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (E X Y : D)

/-- 係数変更したHom因子上の評価。coendの係数変更同型を介して定める。 -/
def endomorphismScalarEvaluation :
    BalancedTensor.obj A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E) (endomorphismHomRight A D E Y))
      (ScalarExtension.leftModule φ (EndomorphismObject E) (endomorphismHomLeft A D E X)) ⟶
        (ScalarExtension.extension φ).obj (homObject A D X Y) :=
  (ScalarExtension.balancedIso φ (EndomorphismObject E)
    (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X)).inv ≫
      (ScalarExtension.extension φ).map (endomorphismEvaluation A D E X Y)

lemma endomorphismScalarEvaluation_ι (b : EndomorphismObject E) :
    BalancedTensor.ι A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
        (ScalarExtension.rightModule φ (EndomorphismObject E) (endomorphismHomRight A D E Y))
        (ScalarExtension.leftModule φ (EndomorphismObject E) (endomorphismHomLeft A D E X)) b ≫
      endomorphismScalarEvaluation φ D E X Y =
    (ScalarExtension.tensorIso φ (homObject A D E Y) (homObject A D X E)).inv ≫
      (ScalarExtension.extension φ).map (endomorphismEvaluationComponent A D E X Y) := by
  unfold endomorphismScalarEvaluation
  rw [ScalarExtension.balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp,
    endomorphismEvaluation_ι]
  rfl

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 任意の環準同型で、導来係数変更の比較射とbalanced合成評価は可換する。 -/
lemma endomorphismDerivedScalarEvaluation_square :
    ScalarExtension.derivedBalancedComparison φ (EndomorphismObject E)
        (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) ≫
      DerivedCategory.Q.map (endomorphismScalarEvaluation φ D E X Y) =
    (ScalarExtension.complexDerivedExtension φ).map
        (DerivedCategory.Q.map (endomorphismEvaluation A D E X Y)) ≫
      (ScalarExtension.complexDerivedExtensionAugmentation φ).app (homObject A D X Y) := by
  unfold ScalarExtension.derivedBalancedComparison endomorphismScalarEvaluation
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact ((ScalarExtension.complexDerivedExtensionAugmentation φ).naturality
    (endomorphismEvaluation A D E X Y)).symm

end SerrePositivity.DifferentialGraded
