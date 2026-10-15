module
public import SerrePositivity.DifferentialGraded.Tensor.Elements
public import SerrePositivity.DifferentialGraded.Module.Representable
public import SerrePositivity.DifferentialGraded.Module.FreeHom

/-! # representableとbalanced tensorのYoneda評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- representableの右作用は、二つのHomの順を交換した豊穣合成。 -/
lemma representable_rightAction (z x y : D) :
    rightAction A D (representable A z) x y =
      (signedSwap (y ⟶[Complex A] z) (x ⟶[Complex A] y)).hom ≫
        eComp (Complex A) x y z := by
  unfold rightAction moduleActionChain
  change (signedSwap (y ⟶[Complex A] z) (x ⟶[Complex A] y)).hom ≫
    uncurryRight (curryRight (eComp (Complex A) x y z)) = _
  rw [uncurryRight_curryRight]

/-- 左加群の作用はrepresentable tensorに対するbalanced族を与える。 -/
def yonedaFamily (z : D) (N : LeftModule A D) :
    BalancedFamily A D (representable A z) N (N.obj z) := by
  refine ⟨fun x => leftAction A D N x z, ?_⟩
  intro x y
  apply triple_ext
  intro a p b n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro h f t
  change (leftAction A D N x z).f n
    ((rightAction A D (representable A z) x y ▷ N.obj x).f n
      (ιTensorObj ((y ⟶[Complex A] z) ⊗ (x ⟶[Complex A] y)) (N.obj x)
        (a + p) b n hn
        (ιTensorObj (y ⟶[Complex A] z) (x ⟶[Complex A] y) a p (a + p) rfl
          (h ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (leftAction A D N y z).f n
      (((y ⟶[Complex A] z) ◁ leftAction A D N x y).f n
        ((α_ (y ⟶[Complex A] z) (x ⟶[Complex A] y) (N.obj x)).hom.f n
          (ιTensorObj ((y ⟶[Complex A] z) ⊗ (x ⟶[Complex A] y)) (N.obj x)
            (a + p) b n hn
            (ιTensorObj (y ⟶[Complex A] z) (x ⟶[Complex A] y) a p (a + p) rfl
              (h ⊗ₜ[A] f) ⊗ₜ[A] t))))
  rw [whiskerRight_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, leftAction_apply]
  change SerrePositivity.DifferentialGraded.leftAction A N
    ((a * p).negOnePow • forward A (n := a + p) f h (by omega)) t (by omega) = _
  rw [leftAction_apply, leftAction_apply]
  have hs : SerrePositivity.DifferentialGraded.leftAction A N (n := n)
      ((a * p).negOnePow • forward A (n := a + p) f h (by omega)) t (by omega) =
    (a * p).negOnePow • SerrePositivity.DifferentialGraded.leftAction A N (n := n)
      (forward A f h (show p + a = a + p by omega)) t (by omega) := by
    simp only [SerrePositivity.DifferentialGraded.leftAction, Units.smul_def,
      map_zsmul]
    rfl
  rw [hs, SerrePositivity.DifferentialGraded.leftAction_forward A N f h t
    (show p + a = a + p by omega) (show b + p = p + b by omega) (by omega)]
  simp only [smul_smul, mul_comm p a, Int.units_mul_self, one_smul]

/-- representable tensorを評価複体へ送るYoneda写像。 -/
def yonedaEvaluation (z : D) (N : LeftModule A D) :
    obj A D (representable A z) N ⟶ N.obj z :=
  desc A D (representable A z) N (yonedaFamily A D z N)

@[reassoc (attr := simp)]
lemma ι_yonedaEvaluation (z : D) (N : LeftModule A D) (x : D) :
    ι A D (representable A z) N x ≫ yonedaEvaluation A D z N = leftAction A D N x z :=
  ι_desc A D (representable A z) N (yonedaFamily A D z N) x

lemma yonedaEvaluation_element (z : D) (N : LeftModule A D) (x : D)
    {p q n : ℤ} (f : GradedHom A x z p) (t : (N.obj x).X q) (hn : p + q = n) :
    (yonedaEvaluation A D z N).f n (element A D (representable A z) N x f t hn) =
      SerrePositivity.DifferentialGraded.leftAction A N f t (by omega) := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (x ⟶[Complex A] z) (N.obj x) p q n hn (f ⊗ₜ[A] t)))
    (ι_yonedaEvaluation A D z N x)
  exact h.trans (leftAction_apply A D N x z p q n hn f t)

/-- 単位Homを挿入するYoneda評価の逆向きの射。 -/
def yonedaInsertion (z : D) (N : LeftModule A D) :
    N.obj z ⟶ obj A D (representable A z) N :=
  freeUnitInsert A z (N.obj z) ≫
    (signedSwap (N.obj z) (z ⟶[Complex A] z)).hom ≫ ι A D (representable A z) N z

lemma yonedaInsertion_apply (z : D) (N : LeftModule A D) (q : ℤ) (t : (N.obj z).X q) :
    (yonedaInsertion A D z N).f q t =
      element A D (representable A z) N z (unitElement A z).val t (zero_add q) := by
  change (ι A D (representable A z) N z).f q
    ((signedSwap (N.obj z) (z ⟶[Complex A] z)).hom.f q
      ((freeUnitInsert A z (N.obj z)).f q t)) = _
  rw [freeUnitInsert_apply, signedSwap_apply]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  rfl

@[reassoc (attr := simp)]
lemma yonedaInsertion_evaluation (z : D) (N : LeftModule A D) :
    yonedaInsertion A D z N ≫ yonedaEvaluation A D z N = 𝟙 (N.obj z) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (yonedaEvaluation A D z N).f q ((yonedaInsertion A D z N).f q t) = t
  rw [yonedaInsertion_apply, yonedaEvaluation_element]
  exact SerrePositivity.DifferentialGraded.leftAction_unit A N z q t

@[reassoc (attr := simp)]
lemma yonedaEvaluation_insertion (z : D) (N : LeftModule A D) :
    yonedaEvaluation A D z N ≫ yonedaInsertion A D z N = 𝟙 _ := by
  apply hom_ext
  intro x
  apply tensorHom_ext
  intro p q n hn
  subst n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f t
  change (yonedaInsertion A D z N).f (p + q)
    ((yonedaEvaluation A D z N).f (p + q) (element A D (representable A z) N x f t rfl)) =
      element A D (representable A z) N x f t rfl
  rw [yonedaEvaluation_element, yonedaInsertion_apply]
  have h := congrArg (fun k => k.f (p + q)
    (ιTensorObj ((z ⟶[Complex A] z) ⊗ (x ⟶[Complex A] z)) (N.obj x) p q (p + q) rfl
      (ιTensorObj (z ⟶[Complex A] z) (x ⟶[Complex A] z) 0 p p (zero_add p)
        ((unitElement A z).val ⊗ₜ[A] f) ⊗ₜ[A] t)))
    (condition A D (representable A z) N x z)
  change (ι A D (representable A z) N x).f (p + q)
    ((rightAction A D (representable A z) x z ▷ N.obj x).f (p + q)
      (ιTensorObj ((z ⟶[Complex A] z) ⊗ (x ⟶[Complex A] z)) (N.obj x) p q (p + q) rfl
        (ιTensorObj (z ⟶[Complex A] z) (x ⟶[Complex A] z) 0 p p (zero_add p)
          ((unitElement A z).val ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (ι A D (representable A z) N z).f (p + q)
      (((z ⟶[Complex A] z) ◁ leftAction A D N x z).f (p + q)
        ((α_ (z ⟶[Complex A] z) (x ⟶[Complex A] z) (N.obj x)).hom.f (p + q)
          (ιTensorObj ((z ⟶[Complex A] z) ⊗ (x ⟶[Complex A] z)) (N.obj x) p q (p + q) rfl
            (ιTensorObj (z ⟶[Complex A] z) (x ⟶[Complex A] z) 0 p p (zero_add p)
              ((unitElement A z).val ⊗ₜ[A] f) ⊗ₜ[A] t)))) at h
  rw [whiskerRight_apply, rightAction_apply, associator_apply_of_sum,
    whiskerLeft_apply, leftAction_apply] at h
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  change element A D (representable A z) N x
    (forward A f (unitElement A z).val (add_zero p)) t rfl = _ at h
  simpa only [element, unit_forward] using h.symm


/-- 右representableとのbalanced tensorは評価複体に同型。 -/
def yonedaIso (z : D) (N : LeftModule A D) :
    obj A D (representable A z) N ≅ N.obj z where
  hom := yonedaEvaluation A D z N
  inv := yonedaInsertion A D z N
  hom_inv_id := yonedaEvaluation_insertion A D z N
  inv_hom_id := yonedaInsertion_evaluation A D z N

end SerrePositivity.DifferentialGraded.BalancedTensor
