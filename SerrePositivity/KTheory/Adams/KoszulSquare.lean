module

public import SerrePositivity.PerfectComplex.KoszulTensor
public import SerrePositivity.KTheory.Adams.TensorPower.TensorSquare
public import SerrePositivity.HomologicalAlgebra.Complex.Cone

/-! # 一元 Koszul 複体のテンソル二乗の写像錐モデル

## 概要

一元 Koszul 複体のテンソル二乗の写像錐によるモデルと、四つの標準生成元の上の符号付きの入れ替え、同次の座標と写像錐の座標の比較を与える。

## 方針

項は有限個なので、座標を明示して等式を確かめる。

## 規約

`KoszulSquareDual`・`KoszulShiftOneModel` は正と負の埋め込みの上にあるので `Adams/KoszulSquareSplitting` に置く。

## 使われ方

`Adams/KoszulSquareSplitting`・`Adams/CyclicTwo` の Koszul の正規化。
-/

@[expose] public noncomputable section

universe u

section KoszulSquareModelPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

namespace Adams

abbrev oneKoszulSquareCone (a : R) :=
  CochainComplex.mappingCone (smulId a (oneKoszulComplex a))

/-- The unit comparison intertwines the scalar maps on the tensor and on Koszul. -/
lemma oneKoszulTensorScalar_unitor (a : R) :
    cochainTensorMap (oneKoszulScalarMap a) (𝟙 (oneKoszulComplex a)) ≫
      (cochainTensorLeftUnitor (oneKoszulComplex a)).hom =
    (cochainTensorLeftUnitor (oneKoszulComplex a)).hom ≫
      smulId a (oneKoszulComplex a) :=
  oneKoszulTensorScalar_leftUnitor a (oneKoszulComplex a)

/-- Tensoring the scalar cone and then removing the tensor unit gives a double cone. -/
def oneKoszulSquareConeIso (a : R) :
    tensorSquare (oneKoszulComplex a) ≅ oneKoszulSquareCone a :=
  oneKoszulTensorConeIso a (oneKoszulComplex a)

lemma oneKoszulSquareCone_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) : IsZero ((oneKoszulSquareCone a).X n) := by
  apply (CochainComplex.mappingCone.isZero_X_iff _ n).mpr
  exact ⟨oneKoszul_isZero_X_other a (n + 1) (by omega),
    oneKoszul_isZero_X_other a n (by omega)⟩

lemma oneKoszulSquare_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) :
    IsZero ((tensorSquare (oneKoszulComplex a)).X n) :=
  (oneKoszulSquareCone_isZero_X_other a n hn).of_iso
    ((HomologicalComplex.eval _ _ n).mapIso (oneKoszulSquareConeIso a))

abbrev oneKoszulSquareConeBottom (a : R) :
    ModuleCat.of R R ⟶ (oneKoszulSquareCone a).X 0 :=
  (oneKoszulXZeroIso a).inv ≫ (CochainComplex.mappingCone.inr
    (smulId a (oneKoszulComplex a))).f 0

abbrev oneKoszulSquareConeLeft (a : R) :
    ModuleCat.of R R ⟶ (oneKoszulSquareCone a).X (-1) :=
  (oneKoszulXZeroIso a).inv ≫ (CochainComplex.mappingCone.inl
    (smulId a (oneKoszulComplex a))).v 0 (-1) (by omega)

abbrev oneKoszulSquareConeRight (a : R) :
    ModuleCat.of R R ⟶ (oneKoszulSquareCone a).X (-1) :=
  (oneKoszulXNegOneIso a).inv ≫ (CochainComplex.mappingCone.inr
    (smulId a (oneKoszulComplex a))).f (-1)

abbrev oneKoszulSquareConeTop (a : R) :
    ModuleCat.of R R ⟶ (oneKoszulSquareCone a).X (-2) :=
  (oneKoszulXNegOneIso a).inv ≫ (CochainComplex.mappingCone.inl
    (smulId a (oneKoszulComplex a))).v (-1) (-2) (by omega)

lemma oneKoszulSquareConeLeft_d (a : R) :
    oneKoszulSquareConeLeft a ≫ (oneKoszulSquareCone a).d (-1) 0 =
      a • oneKoszulSquareConeBottom a := by
  have hd : (oneKoszulComplex a).d 0 1 = 0 :=
    (oneKoszul_isZero_X_other a 1 (by omega)).eq_of_tgt _ _
  change (oneKoszulXZeroIso a).inv ≫
    (CochainComplex.mappingCone.inl (smulId a (oneKoszulComplex a))).v 0 (-1) (by omega) ≫
    (oneKoszulSquareCone a).d (-1) 0 = _
  rw [CochainComplex.mappingCone.inl_v_d (smulId a (oneKoszulComplex a))
    0 (-1) 1 (by omega) (by omega)]
  simp [hd, smulId, oneKoszulSquareConeBottom, Linear.smul_comp, Linear.comp_smul]

lemma oneKoszulSquareConeRight_d (a : R) :
    oneKoszulSquareConeRight a ≫ (oneKoszulSquareCone a).d (-1) 0 =
      a • oneKoszulSquareConeBottom a := by
  change (oneKoszulXNegOneIso a).inv ≫
    (CochainComplex.mappingCone.inr (smulId a (oneKoszulComplex a))).f (-1) ≫
    (oneKoszulSquareCone a).d (-1) 0 = _
  rw [CochainComplex.mappingCone.inr_f_d, ← Category.assoc, oneKoszul_generator_d]
  simp [oneKoszulSquareConeBottom, Linear.smul_comp]

lemma oneKoszulSquareConeTop_d (a : R) :
    oneKoszulSquareConeTop a ≫ (oneKoszulSquareCone a).d (-2) (-1) =
      a • oneKoszulSquareConeRight a - a • oneKoszulSquareConeLeft a := by
  change (oneKoszulXNegOneIso a).inv ≫
    (CochainComplex.mappingCone.inl (smulId a (oneKoszulComplex a))).v (-1) (-2) (by omega) ≫
    (oneKoszulSquareCone a).d (-2) (-1) = _
  rw [CochainComplex.mappingCone.inl_v_d (smulId a (oneKoszulComplex a))
    (-1) (-2) 0 (by omega) (by omega), Preadditive.comp_sub,
    ← Category.assoc (oneKoszulXNegOneIso a).inv ((oneKoszulComplex a).d (-1) 0),
    oneKoszul_generator_d]
  simp [smulId, oneKoszulSquareConeLeft, oneKoszulSquareConeRight,
    Linear.smul_comp, Linear.comp_smul]

end Adams
end SerrePositivity

end KoszulSquareModelPart

section KoszulSquareSwapPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
variable {R : Type u} [CommRing R]

namespace Adams

abbrev scalarTensorDiagonal : ModuleCat.of R R ⟶ ModuleCat.of R R ⊗ ModuleCat.of R R :=
  (λ_ (ModuleCat.of R R)).inv

lemma scalarTensorDiagonal_braiding :
    scalarTensorDiagonal (R := R) ≫
      (β_ (ModuleCat.of R R) (ModuleCat.of R R)).hom = scalarTensorDiagonal := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change r ⊗ₜ[R] (1 : R) = (1 : R) ⊗ₜ[R] r
  simpa only [smul_eq_mul, mul_one] using
    (TensorProduct.smul_tmul (R := R) r (1 : R) (1 : R))

lemma scalarTensorDiagonal_tensor_braiding {A B : ModuleCat.{u} R}
    (f : ModuleCat.of R R ⟶ A) (g : ModuleCat.of R R ⟶ B) :
    scalarTensorDiagonal ≫ (f ⊗ₘ g) ≫ (β_ A B).hom =
      scalarTensorDiagonal ≫ (g ⊗ₘ f) := by
  rw [BraidedCategory.braiding_naturality, ← Category.assoc, scalarTensorDiagonal_braiding]

def oneKoszulTensorGenerator (a : R) (i j n : ℤ) (h : i + j = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j) :
    ModuleCat.of R R ⟶ (tensorSquare (oneKoszulComplex a)).X n :=
  scalarTensorDiagonal ≫ (f ⊗ₘ g) ≫ ιTensorObj (oneKoszulComplex a) (oneKoszulComplex a) i j n h

lemma oneKoszulTensorGenerator_swap (a : R) (i j n : ℤ) (h : i + j = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j) :
    oneKoszulTensorGenerator a i j n h f g ≫ (tensorSquareSwap (oneKoszulComplex a)).f n =
      (i * j).negOnePow • oneKoszulTensorGenerator a j i n (by omega) g f := by
  dsimp [oneKoszulTensorGenerator]
  simp only [Category.assoc]
  rw [ιTensorObj_tensorSquareSwap]
  rw [Linear.comp_units_smul, Linear.comp_units_smul]
  congr 1
  rw [← Category.assoc (f ⊗ₘ g), ← Category.assoc,
    scalarTensorDiagonal_tensor_braiding]
  exact Category.assoc _ _ _

abbrev oneKoszulSquareBottom (a : R) :=
  oneKoszulTensorGenerator a 0 0 0 rfl (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv

abbrev oneKoszulSquareLeft (a : R) :=
  oneKoszulTensorGenerator a (-1) 0 (-1) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv

abbrev oneKoszulSquareRight (a : R) :=
  oneKoszulTensorGenerator a 0 (-1) (-1) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv

abbrev oneKoszulSquareTop (a : R) :=
  oneKoszulTensorGenerator a (-1) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulSquareBottom_swap (a : R) :
    oneKoszulSquareBottom a ≫ (tensorSquareSwap (oneKoszulComplex a)).f 0 =
      oneKoszulSquareBottom a := by
  simpa using oneKoszulTensorGenerator_swap a 0 0 0 rfl
    (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv

lemma oneKoszulSquareLeft_swap (a : R) :
    oneKoszulSquareLeft a ≫ (tensorSquareSwap (oneKoszulComplex a)).f (-1) =
      oneKoszulSquareRight a := by
  simpa using oneKoszulTensorGenerator_swap a (-1) 0 (-1) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv

lemma oneKoszulSquareRight_swap (a : R) :
    oneKoszulSquareRight a ≫ (tensorSquareSwap (oneKoszulComplex a)).f (-1) =
      oneKoszulSquareLeft a := by
  simpa using oneKoszulTensorGenerator_swap a 0 (-1) (-1) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulSquareTop_swap (a : R) :
    oneKoszulSquareTop a ≫ (tensorSquareSwap (oneKoszulComplex a)).f (-2) =
      -oneKoszulSquareTop a := by
  simpa using oneKoszulTensorGenerator_swap a (-1) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulSquarePositive_swap (a : R) :
    (oneKoszulSquareLeft a + oneKoszulSquareRight a) ≫
      (tensorSquareSwap (oneKoszulComplex a)).f (-1) =
    oneKoszulSquareLeft a + oneKoszulSquareRight a := by
  rw [Preadditive.add_comp, oneKoszulSquareLeft_swap, oneKoszulSquareRight_swap, add_comm]

lemma oneKoszulSquareNegative_swap (a : R) :
    (oneKoszulSquareLeft a - oneKoszulSquareRight a) ≫
      (tensorSquareSwap (oneKoszulComplex a)).f (-1) =
    -(oneKoszulSquareLeft a - oneKoszulSquareRight a) := by
  rw [Preadditive.sub_comp, oneKoszulSquareLeft_swap, oneKoszulSquareRight_swap, neg_sub]

end Adams
end SerrePositivity

end KoszulSquareSwapPart

section KoszulSquareCoordinatesPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex MonoidalCategory
variable {R : Type u} [CommRing R]

namespace Adams

lemma scalarTensorDiagonal_unit_inclusion (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (j : ℤ) (g : ModuleCat.of R R ⟶ Q.X j) :
    scalarTensorDiagonal ≫ ((oneKoszulUnitSelfIso (R := R)).inv ⊗ₘ g) ≫
      ιTensorObj (oneKoszulUnit (R := R)) Q 0 j j (by omega) =
    g ≫ (cochainTensorLeftUnitor Q).inv.f j := by
  have hi : (cochainTensorLeftUnitor Q).inv.f j =
      (λ_ (Q.X j)).inv ≫ ((oneKoszulUnitSelfIso (R := R)).inv ▷ Q.X j) ≫
        ιTensorObj (oneKoszulUnit (R := R)) Q 0 j j (by omega) :=
    HomologicalComplex.leftUnitor'_inv Q j
  rw [hi, tensorHom_def']
  change (λ_ (ModuleCat.of R R)).inv ≫ _ ≫ _ = _
  simp only [Category.assoc]
  have hh : (λ_ (ModuleCat.of R R)).inv ≫ (ModuleCat.of R R ◁ g) =
      g ≫ (λ_ (Q.X j)).inv := (leftUnitor_inv_naturality g).symm
  rw [← Category.assoc (λ_ (ModuleCat.of R R)).inv (ModuleCat.of R R ◁ g), hh]
  exact Category.assoc _ _ _

@[reassoc]
lemma scalarTensorDiagonal_unit_unitor (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (j : ℤ) (g : ModuleCat.of R R ⟶ Q.X j) :
    scalarTensorDiagonal ≫ ((oneKoszulUnitSelfIso (R := R)).inv ⊗ₘ g) ≫
      ιTensorObj (oneKoszulUnit (R := R)) Q 0 j j (by omega) ≫
      (cochainTensorLeftUnitor Q).hom.f j = g := by
  have h := congrArg (fun f => f.f j) (cochainTensorLeftUnitor Q).inv_hom_id
  calc
    _ = (g ≫ (cochainTensorLeftUnitor Q).inv.f j) ≫
        (cochainTensorLeftUnitor Q).hom.f j := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ (cochainTensorLeftUnitor Q).hom.f j)
          (scalarTensorDiagonal_unit_inclusion Q j g)
    _ = g := by
      rw [Category.assoc, show (cochainTensorLeftUnitor Q).inv.f j ≫
        (cochainTensorLeftUnitor Q).hom.f j = 𝟙 _ from h, Category.comp_id]

@[reassoc]
lemma oneKoszulSquareConeIso_fst (a : R) (n : ℤ) :
    (oneKoszulSquareConeIso a).hom.f n ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v n (n + 1) rfl =
    tensorConeFstX (oneKoszulScalarMap a) (oneKoszulComplex a) n ≫
      (cochainTensorLeftUnitor (oneKoszulComplex a)).hom.f (n + 1) :=
  cochainTensorUnitScalarConeIso_fst a (oneKoszulComplex a) n

@[reassoc]
lemma oneKoszulSquareConeIso_snd (a : R) (n : ℤ) :
    (oneKoszulSquareConeIso a).hom.f n ≫
      (mappingCone.snd (smulId a (oneKoszulComplex a))).v n n (by omega) =
    tensorConeSndX (oneKoszulScalarMap a) (oneKoszulComplex a) n ≫
      (cochainTensorLeftUnitor (oneKoszulComplex a)).hom.f n :=
  cochainTensorUnitScalarConeIso_snd a (oneKoszulComplex a) n

@[reassoc]
lemma oneKoszulTensorGenerator_fst (a : R) (i j n : ℤ) (h : i + j = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j) :
    oneKoszulTensorGenerator a i j n h f g ≫
      tensorConeFstX (oneKoszulScalarMap a) (oneKoszulComplex a) n =
    scalarTensorDiagonal ≫ ((f ≫ (mappingCone.fst (oneKoszulScalarMap a)).1.v
      i (i + 1) rfl) ⊗ₘ g) ≫
      ιTensorObj (oneKoszulUnit (R := R)) (oneKoszulComplex a)
        (i + 1) j (n + 1) (by omega) := by
  change scalarTensorDiagonal ≫ (f ⊗ₘ g) ≫
    ιTensorObj (mappingCone (oneKoszulScalarMap a)) (oneKoszulComplex a) i j n h ≫
      tensorConeFstX (oneKoszulScalarMap a) (oneKoszulComplex a) n = _
  rw [ι_tensorConeFstX]
  rw [tensorHom_comp_whiskerRight_assoc]

@[reassoc]
lemma oneKoszulTensorGenerator_snd (a : R) (i j n : ℤ) (h : i + j = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j) :
    oneKoszulTensorGenerator a i j n h f g ≫
      tensorConeSndX (oneKoszulScalarMap a) (oneKoszulComplex a) n =
    scalarTensorDiagonal ≫ ((f ≫ (mappingCone.snd (oneKoszulScalarMap a)).v
      i i (by omega)) ⊗ₘ g) ≫
      ιTensorObj (oneKoszulUnit (R := R)) (oneKoszulComplex a) i j n h := by
  change scalarTensorDiagonal ≫ (f ⊗ₘ g) ≫
    ιTensorObj (mappingCone (oneKoszulScalarMap a)) (oneKoszulComplex a) i j n h ≫
      tensorConeSndX (oneKoszulScalarMap a) (oneKoszulComplex a) n = _
  rw [ι_tensorConeSndX]
  rw [tensorHom_comp_whiskerRight_assoc]

@[reassoc]
lemma oneKoszulSquareBottom_cone (a : R) :
    oneKoszulSquareBottom a ≫ (oneKoszulSquareConeIso a).hom.f 0 =
      oneKoszulSquareConeBottom a := by
  apply mappingCone.ext_to (smulId a (oneKoszulComplex a)) 0 1 rfl
  · change oneKoszulSquareBottom a ≫ (oneKoszulSquareConeIso a).hom.f 0 ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v 0 (0 + 1) rfl = _
    rw [oneKoszulSquareConeIso_fst]
    simp [Category.assoc, oneKoszulSquareBottom,
      oneKoszulTensorGenerator_fst_assoc, oneKoszulXZeroIso, oneKoszulSquareConeBottom]
  · simp [Category.assoc, oneKoszulSquareConeIso_snd, oneKoszulSquareBottom,
      oneKoszulTensorGenerator_snd_assoc, oneKoszulXZeroIso, oneKoszulSquareConeBottom,
      scalarTensorDiagonal_unit_unitor]

@[reassoc]
lemma oneKoszulSquareLeft_cone (a : R) :
    oneKoszulSquareLeft a ≫ (oneKoszulSquareConeIso a).hom.f (-1) =
      oneKoszulSquareConeLeft a := by
  apply mappingCone.ext_to (smulId a (oneKoszulComplex a)) (-1) 0 (by omega)
  · change oneKoszulSquareLeft a ≫ (oneKoszulSquareConeIso a).hom.f (-1) ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-1) ((-1) + 1) rfl = _
    rw [oneKoszulSquareConeIso_fst]
    simp [Category.assoc, oneKoszulSquareLeft,
      oneKoszulTensorGenerator_fst_assoc, oneKoszulXNegOneIso, oneKoszulSquareConeLeft,
      scalarTensorDiagonal_unit_unitor]
  · simp [Category.assoc, oneKoszulSquareConeIso_snd, oneKoszulSquareLeft,
      oneKoszulTensorGenerator_snd_assoc, oneKoszulXNegOneIso, oneKoszulSquareConeLeft]

@[reassoc]
lemma oneKoszulSquareRight_cone (a : R) :
    oneKoszulSquareRight a ≫ (oneKoszulSquareConeIso a).hom.f (-1) =
      oneKoszulSquareConeRight a := by
  apply mappingCone.ext_to (smulId a (oneKoszulComplex a)) (-1) 0 (by omega)
  · change oneKoszulSquareRight a ≫ (oneKoszulSquareConeIso a).hom.f (-1) ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-1) ((-1) + 1) rfl = _
    rw [oneKoszulSquareConeIso_fst]
    simp [Category.assoc, oneKoszulSquareRight,
      oneKoszulTensorGenerator_fst_assoc, oneKoszulXZeroIso, oneKoszulSquareConeRight]
  · simp [Category.assoc, oneKoszulSquareConeIso_snd, oneKoszulSquareRight,
      oneKoszulTensorGenerator_snd_assoc, oneKoszulXZeroIso, oneKoszulSquareConeRight,
      scalarTensorDiagonal_unit_unitor]

@[reassoc]
lemma oneKoszulSquareTop_cone (a : R) :
    oneKoszulSquareTop a ≫ (oneKoszulSquareConeIso a).hom.f (-2) =
      oneKoszulSquareConeTop a := by
  apply mappingCone.ext_to (smulId a (oneKoszulComplex a)) (-2) (-1) (by omega)
  · change oneKoszulSquareTop a ≫ (oneKoszulSquareConeIso a).hom.f (-2) ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-2) ((-2) + 1) rfl = _
    rw [oneKoszulSquareConeIso_fst]
    simp [Category.assoc, oneKoszulSquareTop,
      oneKoszulTensorGenerator_fst_assoc, oneKoszulXNegOneIso, oneKoszulSquareConeTop,
      scalarTensorDiagonal_unit_unitor]
  · simp [Category.assoc, oneKoszulSquareConeIso_snd, oneKoszulSquareTop,
      oneKoszulTensorGenerator_snd_assoc, oneKoszulXNegOneIso, oneKoszulSquareConeTop]

lemma oneKoszulSquareLeft_d (a : R) :
    oneKoszulSquareLeft a ≫ (tensorSquare (oneKoszulComplex a)).d (-1) 0 =
      a • oneKoszulSquareBottom a := by
  have : IsIso ((oneKoszulSquareConeIso a).hom.f 0) :=
    inferInstanceAs (IsIso (((HomologicalComplex.eval _ _ 0).mapIso
      (oneKoszulSquareConeIso a)).hom))
  apply (cancel_mono ((oneKoszulSquareConeIso a).hom.f 0)).mp
  rw [Category.assoc, ← (oneKoszulSquareConeIso a).hom.comm (-1) 0,
    ← Category.assoc, oneKoszulSquareLeft_cone, oneKoszulSquareConeLeft_d,
    Linear.smul_comp, oneKoszulSquareBottom_cone]

lemma oneKoszulSquareRight_d (a : R) :
    oneKoszulSquareRight a ≫ (tensorSquare (oneKoszulComplex a)).d (-1) 0 =
      a • oneKoszulSquareBottom a := by
  have : IsIso ((oneKoszulSquareConeIso a).hom.f 0) :=
    inferInstanceAs (IsIso (((HomologicalComplex.eval _ _ 0).mapIso
      (oneKoszulSquareConeIso a)).hom))
  apply (cancel_mono ((oneKoszulSquareConeIso a).hom.f 0)).mp
  rw [Category.assoc, ← (oneKoszulSquareConeIso a).hom.comm (-1) 0,
    ← Category.assoc, oneKoszulSquareRight_cone, oneKoszulSquareConeRight_d,
    Linear.smul_comp, oneKoszulSquareBottom_cone]

lemma oneKoszulSquareTop_d (a : R) :
    oneKoszulSquareTop a ≫ (tensorSquare (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulSquareRight a - a • oneKoszulSquareLeft a := by
  have : IsIso ((oneKoszulSquareConeIso a).hom.f (-1)) :=
    inferInstanceAs (IsIso (((HomologicalComplex.eval _ _ (-1)).mapIso
      (oneKoszulSquareConeIso a)).hom))
  apply (cancel_mono ((oneKoszulSquareConeIso a).hom.f (-1))).mp
  rw [Category.assoc, ← (oneKoszulSquareConeIso a).hom.comm (-2) (-1),
    ← Category.assoc, oneKoszulSquareTop_cone, oneKoszulSquareConeTop_d,
    Preadditive.sub_comp, Linear.smul_comp, Linear.smul_comp,
    oneKoszulSquareRight_cone, oneKoszulSquareLeft_cone]

abbrev oneKoszulSquareConeDegreeIso (a : R) (n : ℤ) :=
  (HomologicalComplex.eval _ _ n).mapIso (oneKoszulSquareConeIso a)

@[reassoc]
lemma oneKoszulSquareConeBottom_unmap (a : R) :
    oneKoszulSquareConeBottom a ≫ (oneKoszulSquareConeDegreeIso a 0).inv =
      oneKoszulSquareBottom a :=
  ((Iso.eq_comp_inv (oneKoszulSquareConeDegreeIso a 0)).mpr
    (oneKoszulSquareBottom_cone a)).symm

@[reassoc]
lemma oneKoszulSquareConeLeft_unmap (a : R) :
    oneKoszulSquareConeLeft a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv =
      oneKoszulSquareLeft a :=
  ((Iso.eq_comp_inv (oneKoszulSquareConeDegreeIso a (-1))).mpr
    (oneKoszulSquareLeft_cone a)).symm

@[reassoc]
lemma oneKoszulSquareConeRight_unmap (a : R) :
    oneKoszulSquareConeRight a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv =
      oneKoszulSquareRight a :=
  ((Iso.eq_comp_inv (oneKoszulSquareConeDegreeIso a (-1))).mpr
    (oneKoszulSquareRight_cone a)).symm

@[reassoc]
lemma oneKoszulSquareConeTop_unmap (a : R) :
    oneKoszulSquareConeTop a ≫ (oneKoszulSquareConeDegreeIso a (-2)).inv =
      oneKoszulSquareTop a :=
  ((Iso.eq_comp_inv (oneKoszulSquareConeDegreeIso a (-2))).mpr
    (oneKoszulSquareTop_cone a)).symm

lemma oneKoszulSquareXZero_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorSquare (oneKoszulComplex a)).X 0 ⟶ Y}
    (h : oneKoszulSquareBottom a ≫ f = oneKoszulSquareBottom a ≫ g) : f = g := by
  apply (cancel_epi (oneKoszulSquareConeDegreeIso a 0).inv).mp
  apply mappingCone.ext_from (smulId a (oneKoszulComplex a)) 1 0 rfl
  · exact (oneKoszul_isZero_X_other a 1 (by omega)).eq_of_src _ _
  · apply (cancel_epi (oneKoszulXZeroIso a).inv).mp
    change oneKoszulSquareConeBottom a ≫ (oneKoszulSquareConeDegreeIso a 0).inv ≫ f =
      oneKoszulSquareConeBottom a ≫ (oneKoszulSquareConeDegreeIso a 0).inv ≫ g
    exact (oneKoszulSquareConeBottom_unmap_assoc a f).trans
      (h.trans (oneKoszulSquareConeBottom_unmap_assoc a g).symm)

lemma oneKoszulSquareXNegOne_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorSquare (oneKoszulComplex a)).X (-1) ⟶ Y}
    (hl : oneKoszulSquareLeft a ≫ f = oneKoszulSquareLeft a ≫ g)
    (hr : oneKoszulSquareRight a ≫ f = oneKoszulSquareRight a ≫ g) : f = g := by
  apply (cancel_epi (oneKoszulSquareConeDegreeIso a (-1)).inv).mp
  apply mappingCone.ext_from (smulId a (oneKoszulComplex a)) 0 (-1) (by omega)
  · apply (cancel_epi (oneKoszulXZeroIso a).inv).mp
    change oneKoszulSquareConeLeft a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv ≫ f =
      oneKoszulSquareConeLeft a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv ≫ g
    exact (oneKoszulSquareConeLeft_unmap_assoc a f).trans
      (hl.trans (oneKoszulSquareConeLeft_unmap_assoc a g).symm)
  · apply (cancel_epi (oneKoszulXNegOneIso a).inv).mp
    change oneKoszulSquareConeRight a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv ≫ f =
      oneKoszulSquareConeRight a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv ≫ g
    exact (oneKoszulSquareConeRight_unmap_assoc a f).trans
      (hr.trans (oneKoszulSquareConeRight_unmap_assoc a g).symm)

lemma oneKoszulSquareXNegTwo_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorSquare (oneKoszulComplex a)).X (-2) ⟶ Y}
    (h : oneKoszulSquareTop a ≫ f = oneKoszulSquareTop a ≫ g) : f = g := by
  apply (cancel_epi (oneKoszulSquareConeDegreeIso a (-2)).inv).mp
  apply mappingCone.ext_from (smulId a (oneKoszulComplex a)) (-1) (-2) (by omega)
  · apply (cancel_epi (oneKoszulXNegOneIso a).inv).mp
    change oneKoszulSquareConeTop a ≫ (oneKoszulSquareConeDegreeIso a (-2)).inv ≫ f =
      oneKoszulSquareConeTop a ≫ (oneKoszulSquareConeDegreeIso a (-2)).inv ≫ g
    exact (oneKoszulSquareConeTop_unmap_assoc a f).trans
      (h.trans (oneKoszulSquareConeTop_unmap_assoc a g).symm)
  · exact (oneKoszul_isZero_X_other a (-2) (by omega)).eq_of_src _ _

end Adams
end SerrePositivity

end KoszulSquareCoordinatesPart
