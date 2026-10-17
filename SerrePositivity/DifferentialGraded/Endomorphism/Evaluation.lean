module
public import SerrePositivity.DifferentialGraded.Endomorphism.HomBimodule
public import SerrePositivity.DifferentialGraded.Tensor.BalancedFamilyElements
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionLaws
public import SerrePositivity.DifferentialGraded.Module.RestrictionAction

/-! # End(E)上のbalanced合成評価

Hom(E,Y) ⊗_End(E) Hom(X,E) → Hom(X,Y)を構成する。
tensorの入力順を交換するKoszul符号を明示する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (E : D)

/-- Hom(X,E)の左End(E)作用。 -/
def endomorphismHomLeft (X : D) : LeftModule A (EndomorphismObject E) :=
  (endomorphismInclusion A E).comp (leftRepresentable A X)

/-- balanced評価の余等化前のchain map。 -/
def endomorphismEvaluationComponent (X Y : D) :
    homObject A D E Y ⊗ homObject A D X E ⟶ homObject A D X Y :=
  (signedSwap _ _).hom ≫ eComp (Complex A) X E Y

lemma endomorphismEvaluationComponent_apply (X Y : D) {r s n : ℤ}
    (m : GradedHom A E Y r) (t : GradedHom A X E s) (hn : r + s = n) :
    (endomorphismEvaluationComponent A D E X Y).f n
      (ιTensorObj (homObject A D E Y) (homObject A D X E) r s n hn (m ⊗ₜ[A] t)) =
    (r * s).negOnePow • forward A t m (by omega) := by
  change (eComp (Complex A) X E Y).f n
    ((signedSwap _ _).hom.f n (ιTensorObj (homObject A D E Y) (homObject A D X E)
      r s n hn (m ⊗ₜ[A] t))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  rfl

/-- 合成の結合則はEnd(E)上のbalanced関係を満たす。 -/
def endomorphismEvaluationFamily (X Y : D) :
    BalancedTensor.BalancedFamily A (EndomorphismObject E)
      (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) (homObject A D X Y) := by
  apply BalancedTensor.balancedFamilyMk A (EndomorphismObject E)
    (M := endomorphismHomRight A D E Y) (N := endomorphismHomLeft A D E X)
    (fun _ => endomorphismEvaluationComponent A D E X Y)
  intro x y r p s n hn m f t
  change GradedHom A E Y r at m
  change GradedHom A E E p at f
  change GradedHom A X E s at t
  change (r * p).negOnePow • (endomorphismEvaluationComponent A D E X Y).f n
    (ιTensorObj (homObject A D E Y) (homObject A D X E) (r + p) s n hn
      (moduleAction A (endomorphismHomRight A D E Y) (x := op y) (y := op x) f m rfl ⊗ₜ[A] t)) =
    (endomorphismEvaluationComponent A D E X Y).f n
      (ιTensorObj (homObject A D E Y) (homObject A D X E) r (p + s) n (by omega)
        (m ⊗ₜ[A] SerrePositivity.DifferentialGraded.leftAction A
          (endomorphismHomLeft A D E X) (x := x) (y := y) f t (by omega)))
  rw [endomorphismEvaluationComponent_apply, endomorphismEvaluationComponent_apply]
  have hr : moduleAction A (endomorphismHomRight A D E Y) (x := op y) (y := op x) f m rfl =
      forward A (D := D) (x := E) (y := E) (z := Y) f m (by omega) := rfl
  have hl : SerrePositivity.DifferentialGraded.leftAction A (endomorphismHomLeft A D E X)
      (x := x) (y := y) f t (by omega : s + p = p + s) =
      (p * s).negOnePow • forward A (D := D) (x := X) (y := E) (z := E) t f
        (by omega : s + p = p + s) := by
    exact leftRepresentable_action A X E E f t (by omega)
  rw [hr, hl]
  have hs := forward_assoc_of_sum A (D := D) (w := X) (x := E) (y := E) (z := Y)
    t f m (by omega : s + p = p + s)
    (by omega : p + r = r + p) (by omega : p + s + r = n)
  have hsmul : forward A (D := D) (x := X) (y := E) (z := Y)
      ((p * s).negOnePow • forward A t f (by omega : s + p = p + s)) m
      (by omega : p + s + r = n) =
      (p * s).negOnePow • forward A (forward A t f (by omega : s + p = p + s)) m
        (by omega : p + s + r = n) := by
    simp only [forward, Units.smul_def, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_zsmul]
  rw [hsmul, hs]
  simp only [smul_smul, ← Int.negOnePow_add]
  rw [show r * p + (r + p) * s = r * (p + s) + p * s by ring]

/-- 指定対象を通るbalanced合成評価。 -/
def endomorphismEvaluation (X Y : D) :
    BalancedTensor.obj A (EndomorphismObject E)
      (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) ⟶ homObject A D X Y :=
  BalancedTensor.desc A _ _ _ (endomorphismEvaluationFamily A D E X Y)

@[reassoc (attr := simp)]
lemma endomorphismEvaluation_ι (X Y : D) (b : EndomorphismObject E) :
    BalancedTensor.ι A _ (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) b ≫
      endomorphismEvaluation A D E X Y = endomorphismEvaluationComponent A D E X Y :=
  BalancedTensor.ι_desc A _ _ _ _ b

end SerrePositivity.DifferentialGraded
