module
public import SerrePositivity.DifferentialGraded.Tensor.BalancedFamilyElements
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex

/-! # 中間次数を指定するbalanced族の生成元関係 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma balancedFamily_element_of_sums {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : BalancedFamily A D M N T) (x y : D) {r p s i j n : ℤ}
    (hi : r + p = i) (hj : s + p = j) (hn : i + s = n)
    (m : (M.obj (op y)).X r) (f : GradedHom A x y p) (t : (N.obj x).X s) :
    (r * p).negOnePow • familyElement A D a.val x (moduleAction A M f m hi) t hn =
    familyElement A D a.val y m
      (SerrePositivity.DifferentialGraded.leftAction A N (n := j) f t hj) (by omega) := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) i s n hn
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p i hi
        (m ⊗ₜ[A] f) ⊗ₜ[A] t))) (a.property x y)
  change (a.val x).f n ((rightAction A D M x y ▷ N.obj x).f n
    (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) i s n hn
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p i hi
        (m ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (a.val y).f n ((M.obj (op y) ◁ leftAction A D N x y).f n
      ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom.f n
        (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) i s n hn
          (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p i hi
            (m ⊗ₜ[A] f) ⊗ₜ[A] t)))) at h
  rw [whiskerRight_apply, rightAction_apply,
    associator_apply_of_sums _ _ _ r p s i j n hi (by omega) hn,
    whiskerLeft_apply, leftAction_apply] at h
  simpa only [familyElement, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using h

end SerrePositivity.DifferentialGraded.BalancedTensor
