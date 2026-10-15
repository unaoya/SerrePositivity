module
public import SerrePositivity.DifferentialGraded.Tensor.Elements

/-! # balancedなchain map族の斉次生成元による判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 各対象で与えられたtensor射を純粋斉次元に適用する。 -/
def familyElement {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T) (x : D) {r s n : ℤ}
    (m : (M.obj (op x)).X r) (t : (N.obj x).X s) (hn : r + s = n) : T.X n :=
  (a x).f n (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] t))

lemma balancedFamily_element {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : BalancedFamily A D M N T) (x y : D) {r p s n : ℤ}
    (m : (M.obj (op y)).X r) (f : GradedHom A x y p) (t : (N.obj x).X s)
    (hn : r + p + s = n) :
    (r * p).negOnePow • familyElement A D a.val x (moduleAction A M f m rfl) t hn =
    familyElement A D a.val y m
      (SerrePositivity.DifferentialGraded.leftAction A N
        (n := p + s) f t (by omega)) (by omega) := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
        (m ⊗ₜ[A] f) ⊗ₜ[A] t))) (a.property x y)
  change (a.val x).f n
    ((rightAction A D M x y ▷ N.obj x).f n
      (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (a.val y).f n ((M.obj (op y) ◁ leftAction A D N x y).f n
      ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom.f n
        (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
          (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
            (m ⊗ₜ[A] f) ⊗ₜ[A] t)))) at h
  rw [whiskerRight_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, leftAction_apply] at h
  simpa only [familyElement, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using h

/-- 純粋斉次生成元でのbalanced関係からchain map族のbalanced性を復元する。 -/
def balancedFamilyMk {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T)
    (h : ∀ (x y : D) (r p s n : ℤ) (hn : r + p + s = n)
      (m : (M.obj (op y)).X r) (f : GradedHom A x y p) (t : (N.obj x).X s),
      (r * p).negOnePow • familyElement A D a x (moduleAction A M f m rfl) t hn =
      familyElement A D a y m
        (SerrePositivity.DifferentialGraded.leftAction A N
        (n := p + s) f t (by omega)) (by omega)) :
    BalancedFamily A D M N T := by
  refine ⟨a, ?_⟩
  intro x y
  apply triple_ext
  intro r p s n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro m f t
  change (a x).f n
    ((rightAction A D M x y ▷ N.obj x).f n
      (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (a y).f n ((M.obj (op y) ◁ leftAction A D N x y).f n
      ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom.f n
        (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
          (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
            (m ⊗ₜ[A] f) ⊗ₜ[A] t))))
  rw [whiskerRight_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, leftAction_apply]
  simpa only [familyElement, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using
    h x y r p s n hn m f t

end SerrePositivity.DifferentialGraded.BalancedTensor
