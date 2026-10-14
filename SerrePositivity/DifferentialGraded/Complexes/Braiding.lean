module
public import SerrePositivity.DifferentialGraded.Complexes.CompositionLaws
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # 非有界 Ch(A) の Koszul braiding

既存の cochainTensorSymmetry を自然性・hexagon の証明と共に登録する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 既存の符号付き交換同型を、Ch(A) の braiding として用いる。 -/
abbrev signedSwap (P Q : Complex A) : P ⊗ Q ≅ Q ⊗ P :=
  SerrePositivity.cochainTensorSymmetry P Q

/-- braiding の双次数成分。 -/
@[reassoc]
lemma ι_signedSwap (P Q : Complex A) (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (signedSwap P Q).hom.f n =
      (i * j).negOnePow • ((β_ (P.X i) (Q.X j)).hom ≫
        ιTensorObj Q P j i n (by omega)) :=
  SerrePositivity.ιTensorObj_cochainTensorSymmetry P Q i j n h

/-- 純粋斉次 tensor の交換は (-1)^(ij)。 -/
lemma signedSwap_apply (P Q : Complex A) (i j n : ℤ) (h : i + j = n)
    (x : P.X i) (y : Q.X j) :
    (signedSwap P Q).hom.f n (ιTensorObj P Q i j n h (x ⊗ₜ[A] y)) =
      (i * j).negOnePow • ιTensorObj Q P j i n (by omega) (y ⊗ₜ[A] x) := by
  have he := congr($(ι_signedSwap P Q i j n h).hom (x ⊗ₜ[A] y))
  exact he

/-- signed symmetry は任意の非有界 chain map に関して両変数で自然。 -/
lemma signedSwap_naturality {P P' Q Q' : Complex A} (f : P ⟶ P') (g : Q ⟶ Q') :
    (f ⊗ₘ g) ≫ (signedSwap P' Q').hom = (signedSwap P Q).hom ≫ (g ⊗ₘ f) := by
  apply tensorHom_ext
  intro i j n h
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, ι_tensorHom, Category.assoc, ι_signedSwap,
    ← Category.assoc, ι_signedSwap, Linear.units_smul_comp, Category.assoc, ι_tensorHom]
  rw [Linear.comp_units_smul, ← Category.assoc, ← Category.assoc,
    BraidedCategory.braiding_naturality]

/-- associator の純粋三重斉次 tensor での公式。 -/
lemma associator_apply (P Q T : Complex A) (i j k n : ℤ) (hn : i + j + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).hom.f n
      (ιTensorObj (P ⊗ Q) T (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      ιTensorObj P (Q ⊗ T) i (j + k) n (by omega)
        (x ⊗ₜ[A] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[A] z)) :=
  congr($(ι_associator P Q T i j k n hn).hom (x ⊗ₜ[A] y ⊗ₜ[A] z))

/-- 中間和次数を別名にしても associator の公式は変わらない。 -/
lemma associator_apply_of_sum (P Q T : Complex A) (i j k l n : ℤ)
    (hl : i + j = l) (hn : l + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).hom.f n
      (ιTensorObj (P ⊗ Q) T l k n hn (ιTensorObj P Q i j l hl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      ιTensorObj P (Q ⊗ T) i (j + k) n (by omega)
        (x ⊗ₜ[A] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[A] z)) := by
  subst l
  exact associator_apply P Q T i j k n hn x y z

/-- 右 tensor 射の純粋斉次成分。 -/
lemma whiskerRight_apply {P P' : Complex A} (f : P ⟶ P') (T : Complex A)
    (i j n : ℤ) (hn : i + j = n) (x : P.X i) (z : T.X j) :
    (f ▷ T).f n (ιTensorObj P T i j n hn (x ⊗ₜ[A] z)) =
      ιTensorObj P' T i j n hn (f.f i x ⊗ₜ[A] z) :=
  congr($(ι_whiskerRight f T i j n hn).hom (x ⊗ₜ[A] z))

/-- 左 tensor 射の純粋斉次成分。 -/
lemma whiskerLeft_apply (P : Complex A) {Q Q' : Complex A} (f : Q ⟶ Q')
    (i j n : ℤ) (hn : i + j = n) (x : P.X i) (y : Q.X j) :
    (P ◁ f).f n (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y)) =
      ιTensorObj P Q' i j n hn (x ⊗ₜ[A] f.f j y) :=
  congr($(ι_whiskerLeft P f i j n hn).hom (x ⊗ₜ[A] y))

/-- 右括弧の斉次 inclusion は中間和次数の別名に依存しない。 -/
lemma nested_right_apply (P Q T : Complex A) (i j k l n : ℤ)
    (hl : j + k = l) (hn : i + l = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    ιTensorObj P (Q ⊗ T) i l n hn (x ⊗ₜ[A] ιTensorObj Q T j k l hl (y ⊗ₜ[A] z)) =
      ιTensorObj P (Q ⊗ T) i (j + k) n (by omega)
        (x ⊗ₜ[A] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[A] z)) := by
  subst l
  rfl

/-- 左括弧の斉次 inclusion は中間和次数の別名に依存しない。 -/
lemma nested_left_apply (P Q T : Complex A) (i j k l n : ℤ)
    (hl : i + j = l) (hn : l + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    ιTensorObj (P ⊗ Q) T l k n hn (ιTensorObj P Q i j l hl (x ⊗ₜ[A] y) ⊗ₜ[A] z) =
      ιTensorObj (P ⊗ Q) T (i + j) k n (by omega)
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z) := by
  subst l
  rfl

/-- 左側の hexagon。符号の指数 i(j+k)=ij+ik を三重 tensor で検証する。 -/
lemma signedSwap_hexagon_forward (P Q T : Complex A) :
    (α_ P Q T).hom ≫ (signedSwap P (Q ⊗ T)).hom ≫ (α_ Q T P).hom =
      (signedSwap P Q).hom ▷ T ≫ (α_ Q P T).hom ≫ Q ◁ (signedSwap P T).hom := by
  apply triple_ext
  intro i j k n hn
  simp only [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (α_ Q T P).hom.f n
    ((signedSwap P (Q ⊗ T)).hom.f n
      ((α_ P Q T).hom.f n
        (ιTensorObj (P ⊗ Q) T (i + j) k n hn
          (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)))) =
    (Q ◁ (signedSwap P T).hom).f n
      ((α_ Q P T).hom.f n
        (((signedSwap P Q).hom ▷ T).f n
          (ιTensorObj (P ⊗ Q) T (i + j) k n hn
            (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))))
  rw [associator_apply_of_sum, signedSwap_apply, whiskerRight_apply, signedSwap_apply]
  simp only [Units.smul_def, TensorProduct.smul_tmul, map_zsmul]
  rw [associator_apply_of_sum, associator_apply_of_sum, whiskerLeft_apply, signedSwap_apply]
  simp only [Units.smul_def, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    map_zsmul, smul_smul]
  conv_rhs => rw [nested_right_apply]
  change (i * (j + k)).negOnePow •
    ιTensorObj Q (T ⊗ P) j (k + i) n (by omega)
      (y ⊗ₜ[A] ιTensorObj T P k i (k + i) rfl (z ⊗ₜ[A] x)) =
    ((i * k).negOnePow * (i * j).negOnePow) •
      ιTensorObj Q (T ⊗ P) j (k + i) n (by omega)
        (y ⊗ₜ[A] ιTensorObj T P k i (k + i) rfl (z ⊗ₜ[A] x))
  rw [← Int.negOnePow_add]
  congr 1
  congr 1
  ring
/-- associator の逆を純粋斉次 tensor で評価する。 -/
lemma associator_inv_apply (P Q T : Complex A) (i j k l n : ℤ)
    (hl : j + k = l) (hn : i + l = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).inv.f n
      (ιTensorObj P (Q ⊗ T) i l n hn (x ⊗ₜ[A] ιTensorObj Q T j k l hl (y ⊗ₜ[A] z))) =
      ιTensorObj (P ⊗ Q) T (i + j) k n (by omega)
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z) := by
  subst l
  have he := associator_apply P Q T i j k n (by omega) x y z
  have hh := congrArg (fun t => (α_ P Q T).inv.f n t) he
  have hi := congrArg (fun f => f.f n) (α_ P Q T).hom_inv_id
  have hx := congr($(hi).hom
    (ιTensorObj (P ⊗ Q) T (i + j) k n (by omega)
      (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)))
  change (α_ P Q T).inv.f n ((α_ P Q T).hom.f n _) = _ at hx
  rw [hx] at hh
  exact hh.symm

/-- 右括弧の三重 tensor に対する ext。 -/
lemma rightTriple_ext {P Q T S : Complex A} {f g : P ⊗ (Q ⊗ T) ⟶ S}
    (h : ∀ (i j k n : ℤ) (hn : i + (j + k) = n),
      (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
        ιTensorObj P (Q ⊗ T) i (j + k) n hn ≫ f.f n =
      (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
        ιTensorObj P (Q ⊗ T) i (j + k) n hn ≫ g.f n) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor₂₃.hom_ext (c₁₂ := .up ℤ)
  intro i j k hn
  exact h i j k n (by change i + j + k = n at hn; omega)

/-- 右側の hexagon。符号の指数 (i+j)k=ik+jk を検証する。 -/
lemma signedSwap_hexagon_reverse (P Q T : Complex A) :
    (α_ P Q T).inv ≫ (signedSwap (P ⊗ Q) T).hom ≫ (α_ T P Q).inv =
      P ◁ (signedSwap Q T).hom ≫ (α_ P T Q).inv ≫ (signedSwap P T).hom ▷ Q := by
  apply rightTriple_ext
  intro i j k n hn
  simp only [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold'
  intro x y z
  change (α_ T P Q).inv.f n
    ((signedSwap (P ⊗ Q) T).hom.f n
      ((α_ P Q T).inv.f n
        (ιTensorObj P (Q ⊗ T) i (j + k) n hn
          (x ⊗ₜ[A] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[A] z))))) =
    (((signedSwap P T).hom ▷ Q).f n)
      ((α_ P T Q).inv.f n
        ((P ◁ (signedSwap Q T).hom).f n
          (ιTensorObj P (Q ⊗ T) i (j + k) n hn
            (x ⊗ₜ[A] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[A] z)))))
  rw [associator_inv_apply, signedSwap_apply, whiskerLeft_apply, signedSwap_apply]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul]
  rw [associator_inv_apply, associator_inv_apply, whiskerRight_apply, signedSwap_apply]
  simp only [Units.smul_def, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_zsmul,
    smul_smul]
  conv_rhs => rw [nested_left_apply]
  change ((i + j) * k).negOnePow •
    ιTensorObj (T ⊗ P) Q (k + i) j n (by omega)
      (ιTensorObj T P k i (k + i) rfl (z ⊗ₜ[A] x) ⊗ₜ[A] y) =
    ((j * k).negOnePow * (i * k).negOnePow) •
      ιTensorObj (T ⊗ P) Q (k + i) j n (by omega)
        (ιTensorObj T P k i (k + i) rfl (z ⊗ₜ[A] x) ⊗ₜ[A] y)
  rw [← Int.negOnePow_add]
  congr 1
  congr 1
  ring

/-- 任意可換環上の非有界複体は Koszul 符号による対称モノイダル圏。 -/
instance complexSymmetricCategory : SymmetricCategory (Complex A) where
  braiding := signedSwap
  braiding_naturality_right := by
    intro P Q Q' f
    simpa using signedSwap_naturality (𝟙 P) f
  braiding_naturality_left := by
    intro P P' f Q
    simpa using signedSwap_naturality f (𝟙 Q)
  hexagon_forward := signedSwap_hexagon_forward
  hexagon_reverse := signedSwap_hexagon_reverse
  symmetry := SerrePositivity.cochainTensorSymmetry_hom_comp

/-- 登録した braiding は既存の signed symmetry と同じ同型。 -/
lemma braiding_eq_existing (P Q : Complex A) :
    β_ P Q = SerrePositivity.cochainTensorSymmetry P Q := rfl
end SerrePositivity.DifferentialGraded
