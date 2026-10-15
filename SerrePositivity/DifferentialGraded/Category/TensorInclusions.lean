module
public import SerrePositivity.DifferentialGraded.Category.TensorReindex
public import SerrePositivity.DifferentialGraded.Functor.Components
public import SerrePositivity.DifferentialGraded.Module.FreeHom

/-! # tensor積dg圏への二つの因子の包含

固定対象の閉単位を挿入し、全次数成分で単位・合成を検査する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]

lemma dgTensor_unitElement (x : DGTensorCategory A B C) :
    (unitElement A x).val =
      dgTensorElement A (unitElement A x.1).val (unitElement A x.2).val rfl := by
  change (cycleFromUnit _ (eId (Complex A) x)).val = _
  rw [dgTensor_identity]
  exact unit_tensor_apply (eId (Complex A) x.1) (eId (Complex A) x.2)

def dgTensorFirstHom (c : C) (x y : B) :
    (x ⟶[Complex A] y) ⟶ (x ⟶[Complex A] y) ⊗ (c ⟶[Complex A] c) :=
  freeUnitInsert A c (x ⟶[Complex A] y)

lemma dgTensorFirstHom_apply (c : C) (x y : B) (p : ℤ) (f : GradedHom A x y p) :
    (dgTensorFirstHom A B C c x y).f p f =
      dgTensorElement A (x := (x, c)) (y := (y, c)) f
        (unitElement A c).val (add_zero p) :=
  freeUnitInsert_apply A c (x ⟶[Complex A] y) p f

def dgTensorSecondHom (b : B) (x y : C) :
    (x ⟶[Complex A] y) ⟶ (b ⟶[Complex A] b) ⊗ (x ⟶[Complex A] y) :=
  freeUnitInsert A b (x ⟶[Complex A] y) ≫
    (signedSwap (x ⟶[Complex A] y) (b ⟶[Complex A] b)).hom

lemma dgTensorSecondHom_apply (b : B) (x y : C) (p : ℤ) (f : GradedHom A x y p) :
    (dgTensorSecondHom A B C b x y).f p f =
      dgTensorElement A (x := (b, x)) (y := (b, y))
        (unitElement A b).val f (zero_add p) := by
  change (signedSwap (x ⟶[Complex A] y) (b ⟶[Complex A] b)).hom.f p
    ((freeUnitInsert A b (x ⟶[Complex A] y)).f p f) = _
  rw [freeUnitInsert_apply, signedSwap_apply]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  rfl

/-- 固定した第二対象の単位を挿入するdg関手。 -/
def dgTensorIncludeFirst (c : C) : DGFunctor A B (DGTensorCategory A B C) :=
  DGFunctor.ofHomMaps A (D := B) (E := DGTensorCategory A B C)
    (fun b => ((b, c) : DGTensorCategory A B C)) (dgTensorFirstHom A B C c)
    (fun b => (dgTensorFirstHom_apply A B C c b b 0 (unitElement A b).val).trans
      (dgTensor_unitElement A B C (b, c)).symm)
    (fun x y z p q n hn f g => by
      have h := dgTensor_forward_of_sum A (x := (x, c)) (y := (y, c)) (z := (z, c))
        f (unitElement A c).val g (unitElement A c).val
        (add_zero p) (add_zero q) hn rfl hn
      have hs : dgTensorElement A (x := (x, c)) (y := (z, c)) (forward A f g hn)
          (unitElement A c).val (add_zero n) =
        forward A (D := DGTensorCategory A B C) (x := ((x, c) : DGTensorCategory A B C))
          (y := ((y, c) : DGTensorCategory A B C)) (z := ((z, c) : DGTensorCategory A B C))
          (dgTensorElement A f (unitElement A c).val (add_zero p))
          (dgTensorElement A g (unitElement A c).val (add_zero q)) hn := by
        simpa only [zero_mul, Int.negOnePow_zero, one_smul, forward_unit] using h.symm
      exact (dgTensorFirstHom_apply A B C c x z n (forward A f g hn)).trans
        (hs.trans (congrArg₂ (fun a b => forward A (D := DGTensorCategory A B C)
          (x := ((x, c) : DGTensorCategory A B C))
          (y := ((y, c) : DGTensorCategory A B C)) (z := ((z, c) : DGTensorCategory A B C)) a b hn)
          (dgTensorFirstHom_apply A B C c x y p f)
          (dgTensorFirstHom_apply A B C c y z q g)).symm))

/-- 固定した第一対象の単位を挿入するdg関手。 -/
def dgTensorIncludeSecond (b : B) : DGFunctor A C (DGTensorCategory A B C) :=
  DGFunctor.ofHomMaps A (D := C) (E := DGTensorCategory A B C)
    (fun c => ((b, c) : DGTensorCategory A B C)) (dgTensorSecondHom A B C b)
    (fun c => (dgTensorSecondHom_apply A B C b c c 0 (unitElement A c).val).trans
      (dgTensor_unitElement A B C (b, c)).symm)
    (fun x y z p q n hn f g => by
      have h := dgTensor_forward_of_sum A (x := (b, x)) (y := (b, y)) (z := (b, z))
        (unitElement A b).val f (unitElement A b).val g
        (zero_add p) (zero_add q) rfl hn hn
      have hs : dgTensorElement A (x := (b, x)) (y := (b, z)) (unitElement A b).val
          (forward A f g hn) (zero_add n) =
        forward A (D := DGTensorCategory A B C) (x := ((b, x) : DGTensorCategory A B C))
          (y := ((b, y) : DGTensorCategory A B C)) (z := ((b, z) : DGTensorCategory A B C))
          (dgTensorElement A (unitElement A b).val f (zero_add p))
          (dgTensorElement A (unitElement A b).val g (zero_add q)) hn := by
        simpa only [mul_zero, Int.negOnePow_zero, one_smul, forward_unit] using h.symm
      exact (dgTensorSecondHom_apply A B C b x z n (forward A f g hn)).trans
        (hs.trans (congrArg₂ (fun a b' => forward A (D := DGTensorCategory A B C)
          (x := ((b, x) : DGTensorCategory A B C))
          (y := ((b, y) : DGTensorCategory A B C)) (z := ((b, z) : DGTensorCategory A B C)) a b' hn)
          (dgTensorSecondHom_apply A B C b x y p f)
          (dgTensorSecondHom_apply A B C b y z q g)).symm))

end SerrePositivity.DifferentialGraded
