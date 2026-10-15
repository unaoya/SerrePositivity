module
public import SerrePositivity.DifferentialGraded.Tensor.Yoneda
public import SerrePositivity.DifferentialGraded.Module.LeftRepresentable
public import SerrePositivity.DifferentialGraded.Module.Yoneda
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex

/-! # 左representableとbalanced tensorの評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右加群の作用は左representableに対するbalanced族を与える。 -/
def leftYonedaFamily (z : D) (M : RightModule A D) :
    BalancedFamily A D M (leftRepresentable A z) (M.obj (op z)) := by
  refine ⟨fun x => rightAction A D M z x, ?_⟩
  intro x y
  apply triple_ext
  intro a p b n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro m f h
  change GradedHom A z x b at h
  let la : (x ⟶[Complex A] y) ⊗ (z ⟶[Complex A] x) ⟶ (z ⟶[Complex A] y) :=
    leftAction A D (leftRepresentable A z) x y
  have hl := leftAction_apply A D (leftRepresentable A z) x y p b (p + b) rfl f h
  change la.f (p + b)
    (ιTensorObj (x ⟶[Complex A] y) (z ⟶[Complex A] x) p b (p + b) rfl (f ⊗ₜ[A] h)) = _ at hl
  change (rightAction A D M z x).f n
    ((rightAction A D M x y ▷ (z ⟶[Complex A] x)).f n
      (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (z ⟶[Complex A] x)
        (a + p) b n hn
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] h))) =
    (rightAction A D M z y).f n
      ((M.obj (op y) ◁ la).f n
        ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (z ⟶[Complex A] x)).hom.f n
          (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (z ⟶[Complex A] x)
            (a + p) b n hn
            (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl
              (m ⊗ₜ[A] f) ⊗ₜ[A] h))))
  rw [whiskerRight_apply, rightAction_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, hl, leftRepresentable_action]
  rw [rightAction_apply]
  have hs : moduleAction A M h ((a * p).negOnePow • moduleAction A M f m rfl) hn =
      (a * p).negOnePow • moduleAction A M h (moduleAction A M f m rfl) hn := by
    simp only [moduleAction, Units.smul_def, map_zsmul]
  rw [hs]
  have ht : moduleAction A M (x := op y) (y := op z)
      ((p * b).negOnePow • forward A (D := D) (x := z) (y := x) (z := y) h f
        (show b + p = p + b by omega)) m
      (show a + (p + b) = n by omega) =
    (p * b).negOnePow • moduleAction A M (x := op y) (y := op z)
      (forward A (D := D) (x := z) (y := x) (z := y) h f
        (show b + p = p + b by omega)) m (by omega) := by
    simp only [moduleAction, Units.smul_def, map_zsmul]
    rfl
  rw [ht]
  have hc := moduleAction_representable A y M (op x) (op z) b p a (p + b) n (a + p)
    rfl rfl (by omega) h f m
  change moduleAction A M (x := op y) (y := op z)
    (forward A (D := D) (x := z) (y := x) (z := y) h f (by omega)) m (by omega) = _ at hc
  rw [hc]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

/-- 左representableとのtensorから右加群の評価への射。 -/
def leftYonedaEvaluation (z : D) (M : RightModule A D) :
    obj A D M (leftRepresentable A z) ⟶ M.obj (op z) :=
  desc A D M (leftRepresentable A z) (leftYonedaFamily A D z M)

@[reassoc (attr := simp)]
lemma ι_leftYonedaEvaluation (z : D) (M : RightModule A D) (x : D) :
    ι A D M (leftRepresentable A z) x ≫ leftYonedaEvaluation A D z M =
      rightAction A D M z x :=
  ι_desc A D M (leftRepresentable A z) (leftYonedaFamily A D z M) x

lemma leftYonedaEvaluation_element (z : D) (M : RightModule A D) (x : D)
    {a p n : ℤ} (m : (M.obj (op x)).X a) (f : GradedHom A z x p) (hn : a + p = n) :
    (leftYonedaEvaluation A D z M).f n (element A D M (leftRepresentable A z) x m f hn) =
      (a * p).negOnePow • moduleAction A M f m hn := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p n hn (m ⊗ₜ[A] f)))
    (ι_leftYonedaEvaluation A D z M x)
  exact h.trans (rightAction_apply A D M z x a p n hn m f)

/-- 右側に単位Homを挿入する逆向きの射。 -/
def leftYonedaInsertion (z : D) (M : RightModule A D) :
    M.obj (op z) ⟶ obj A D M (leftRepresentable A z) :=
  freeUnitInsert A z (M.obj (op z)) ≫ ι A D M (leftRepresentable A z) z

lemma leftYonedaInsertion_apply (z : D) (M : RightModule A D) (a : ℤ)
    (m : (M.obj (op z)).X a) :
    (leftYonedaInsertion A D z M).f a m =
      element A D M (leftRepresentable A z) z m (unitElement A z).val (add_zero a) := by
  change (ι A D M (leftRepresentable A z) z).f a
    ((freeUnitInsert A z (M.obj (op z))).f a m) = _
  rw [freeUnitInsert_apply]
  rfl

@[reassoc (attr := simp)]
lemma leftYonedaInsertion_evaluation (z : D) (M : RightModule A D) :
    leftYonedaInsertion A D z M ≫ leftYonedaEvaluation A D z M = 𝟙 (M.obj (op z)) := by
  apply HomologicalComplex.hom_ext
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (leftYonedaEvaluation A D z M).f a ((leftYonedaInsertion A D z M).f a m) = m
  rw [leftYonedaInsertion_apply, leftYonedaEvaluation_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op z) a m

@[reassoc (attr := simp)]
lemma leftYonedaEvaluation_insertion (z : D) (M : RightModule A D) :
    leftYonedaEvaluation A D z M ≫ leftYonedaInsertion A D z M = 𝟙 _ := by
  apply hom_ext
  intro x
  apply tensorHom_ext
  intro a p n hn
  subst n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m f
  change (leftYonedaInsertion A D z M).f (a + p)
    ((leftYonedaEvaluation A D z M).f (a + p)
      (element A D M (leftRepresentable A z) x m f rfl)) =
    element A D M (leftRepresentable A z) x m f rfl
  rw [leftYonedaEvaluation_element]
  simp only [Units.smul_def, map_zsmul]
  rw [leftYonedaInsertion_apply]
  let la : (z ⟶[Complex A] x) ⊗ (z ⟶[Complex A] z) ⟶ (z ⟶[Complex A] x) :=
    leftAction A D (leftRepresentable A z) z x
  have hl := leftAction_apply A D (leftRepresentable A z) z x p 0 p (add_zero p)
    f (unitElement A z).val
  change la.f p (ιTensorObj (z ⟶[Complex A] x) (z ⟶[Complex A] z) p 0 p
    (add_zero p) (f ⊗ₜ[A] (unitElement A z).val)) = _ at hl
  have h := congrArg (fun k => k.f (a + p)
    (ιTensorObj (M.obj (op x) ⊗ (z ⟶[Complex A] x)) (z ⟶[Complex A] z)
      (a + p) 0 (a + p) (add_zero _)
      (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p (a + p) rfl
        (m ⊗ₜ[A] f) ⊗ₜ[A] (unitElement A z).val)))
    (condition A D M (leftRepresentable A z) z x)
  change (ι A D M (leftRepresentable A z) z).f (a + p)
    ((rightAction A D M z x ▷ (z ⟶[Complex A] z)).f (a + p)
      (ιTensorObj (M.obj (op x) ⊗ (z ⟶[Complex A] x)) (z ⟶[Complex A] z)
        (a + p) 0 (a + p) (add_zero _)
        (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p (a + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] (unitElement A z).val))) =
    (ι A D M (leftRepresentable A z) x).f (a + p)
      ((M.obj (op x) ◁ la).f (a + p)
        ((α_ (M.obj (op x)) (z ⟶[Complex A] x) (z ⟶[Complex A] z)).hom.f (a + p)
          (ιTensorObj (M.obj (op x) ⊗ (z ⟶[Complex A] x)) (z ⟶[Complex A] z)
            (a + p) 0 (a + p) (add_zero _)
            (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p (a + p) rfl
              (m ⊗ₜ[A] f) ⊗ₜ[A] (unitElement A z).val)))) at h
  rw [whiskerRight_apply, rightAction_apply,
    associator_apply_of_sums _ _ _ a p 0 (a + p) p (a + p) rfl (add_zero p),
    whiskerLeft_apply, hl, leftRepresentable_action] at h
  change ((a * p).negOnePow : ℤ) •
    (ι A D M (leftRepresentable A z) z).f (a + p)
      (ιTensorObj (M.obj (op z)) (z ⟶[Complex A] z) (a + p) 0 (a + p) (add_zero _)
        (moduleAction A M f m rfl ⊗ₜ[A] (unitElement A z).val)) =
    (ι A D M (leftRepresentable A z) x).f (a + p)
      (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p (a + p) rfl (m ⊗ₜ[A] f))
  simpa only [mul_zero, Int.negOnePow_zero, one_smul, forward_unit,
    Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using h

/-- 左representableとのbalanced tensorも評価複体に同型。 -/
def leftYonedaIso (z : D) (M : RightModule A D) :
    obj A D M (leftRepresentable A z) ≅ M.obj (op z) where
  hom := leftYonedaEvaluation A D z M
  inv := leftYonedaInsertion A D z M
  hom_inv_id := leftYonedaEvaluation_insertion A D z M
  inv_hom_id := leftYonedaInsertion_evaluation A D z M

end SerrePositivity.DifferentialGraded.BalancedTensor
