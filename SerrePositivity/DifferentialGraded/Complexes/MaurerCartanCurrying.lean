module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Complexes.MaurerCartanCurrying

## 概要
13 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Currying（旧 SerrePositivity/DifferentialGraded/Complexes/Currying.lean） -/

/-! # 非有界 tensor と線形 Hom の転置

最初に Q⊗P → T と Q → linearHomComplex(P,T) の符号なし転置を構成する。
微分の符号は tensor 第一因子の Q 次数に一致する。
-/

@[expose] public section Currying
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {P Q T : Complex A}

/-- Q⊗P → T の次数 q 成分を、P の全次数を走る線形射の族に転置する。 -/
def curryComponent (f : Q ⊗ P ⟶ T) (q : ℤ) : Q.X q →ₗ[A] Homogeneous P T q where
  toFun x := Cochain.mk (fun i j hij =>
    ModuleCat.ofHom (TensorProduct.curry (ιTensorObj Q P q i j (by omega) ≫ f.f j).hom x))
  map_add' x x' := by
    apply Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    exact (TensorProduct.curry (ιTensorObj Q P q i j (by omega) ≫ f.f j).hom).map_add x x'
  map_smul' a x := by
    apply Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    exact (TensorProduct.curry (ιTensorObj Q P q i j (by omega) ≫ f.f j).hom).map_smul a x

/-- 転置の評価公式。 -/
lemma curryComponent_apply (f : Q ⊗ P ⟶ T) (q i j : ℤ) (hij : i + q = j)
    (x : Q.X q) (y : P.X i) :
    (curryComponent f q x).v i j hij y =
      f.f j (ιTensorObj Q P q i j (by omega) (x ⊗ₜ[A] y)) := rfl

/-- 全次数 n の tensor 微分を純粋斉次元上で評価する。 -/
lemma tensor_d_apply (P Q : Complex A) (i j n : ℤ) (hn : i + j = n)
    (x : P.X i) (y : Q.X j) :
    (P ⊗ Q).d n (n + 1) (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y)) =
      ιTensorObj P Q (i + 1) j (n + 1) (by omega) (P.d i (i + 1) x ⊗ₜ[A] y) +
      i.negOnePow • ιTensorObj P Q i (j + 1) (n + 1) (by omega)
        (x ⊗ₜ[A] Q.d j (j + 1) y) :=
  SerrePositivity.cochainTensor_d_apply_ι P Q i j n hn x y

/-- 転置した成分は Hom 微分と可換。 -/
lemma curryComponent_d (f : Q ⊗ P ⟶ T) (q : ℤ) (x : Q.X q) :
    δ q (q + 1) (curryComponent f q x) =
      curryComponent f (q + 1) (Q.d q (q + 1) x) := by
  apply Cochain.ext
  intro i j hij
  rw [δ_v q (q + 1) rfl _ i j hij (i + q) (i + 1) (by omega) rfl]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain rfl : j = i + q + 1 := by omega
  have he := f.comm (i + q) (i + q + 1)
  have hv := congr($(he).hom (ιTensorObj Q P q i (i + q) (by omega) (x ⊗ₜ[A] y)))
  change T.d (i + q) (i + q + 1)
    (f.f (i + q) (ιTensorObj Q P q i (i + q) (by omega) (x ⊗ₜ[A] y))) =
    f.f (i + q + 1) ((Q ⊗ P).d (i + q) (i + q + 1)
      (ιTensorObj Q P q i (i + q) (by omega) (x ⊗ₜ[A] y))) at hv
  rw [tensor_d_apply, map_add] at hv
  simp only [Units.smul_def, map_zsmul] at hv
  change T.d (i + q) (i + q + 1)
    (f.f (i + q) (ιTensorObj Q P q i (i + q) (by omega) (x ⊗ₜ[A] y))) =
    f.f (i + q + 1) (ιTensorObj Q P (q + 1) i (i + q + 1) (by omega)
      (Q.d q (q + 1) x ⊗ₜ[A] y)) +
    q.negOnePow • f.f (i + q + 1)
      (ιTensorObj Q P q (i + 1) (i + q + 1) (by omega) (x ⊗ₜ[A] P.d i (i + 1) y)) at hv
  change T.d (i + q) (i + q + 1)
    (f.f (i + q) (ιTensorObj Q P q i (i + q) (by omega) (x ⊗ₜ[A] y))) +
    (q + 1).negOnePow • f.f (i + q + 1)
      (ιTensorObj Q P q (i + 1) (i + q + 1) (by omega) (x ⊗ₜ[A] P.d i (i + 1) y)) =
    f.f (i + q + 1) (ιTensorObj Q P (q + 1) i (i + q + 1) (by omega)
      (Q.d q (q + 1) x ⊗ₜ[A] y))
  rw [hv, Int.negOnePow_succ, Units.neg_smul]
  abel

/-- 符号なし右 tensor 転置の chain map。 -/
def curryRight (f : Q ⊗ P ⟶ T) : Q ⟶ homComplex A P T where
  f q := ModuleCat.ofHom (curryComponent f q)
  comm' q r hqr := by
    obtain rfl : r = q + 1 := hqr.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact curryComponent_d f q
/-- 転置した射の純粋tensor上の評価。 -/
def uncurryComponent (t : Q ⟶ homComplex A P T) (i j n : ℤ) (hn : i + j = n) :
    Q.X i ⊗ P.X j ⟶ T.X n :=
  ModuleCat.ofHom (TensorProduct.lift
    { toFun x := ((t.f i x).v j n (by omega)).hom
      map_add' x x' := by
        apply LinearMap.ext
        intro y
        change (t.f i (x + x')).v j n (by omega) y = _
        rw [map_add, Cochain.add_v]
        rfl
      map_smul' a x := by
        apply LinearMap.ext
        intro y
        change (t.f i (a • x)).v j n (by omega) y = _
        rw [map_smul, Cochain.smul_v]
        rfl })

/-- 逆転置の成分は tensor 微分と可換。 -/
lemma uncurryComponent_d (t : Q ⟶ homComplex A P T) (i j : ℤ) :
    uncurryComponent t i j (i + j) rfl ≫ T.d (i + j) (i + j + 1) =
      (Q.d i (i + 1) ▷ P.X j) ≫ uncurryComponent t (i + 1) j (i + j + 1) (by omega) +
      i.negOnePow • ((Q.X i ◁ P.d j (j + 1)) ≫
        uncurryComponent t i (j + 1) (i + j + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  have ht := congr($(t.comm i (i + 1)).hom x)
  change δ i (i + 1) (t.f i x) = t.f (i + 1) (Q.d i (i + 1) x) at ht
  have hv := Cochain.congr_v ht j (i + j + 1) (by omega)
  rw [δ_v i (i + 1) rfl _ j (i + j + 1) (by omega) (i + j) (j + 1) (by omega) rfl] at hv
  have he := congr($(hv).hom y)
  change T.d (i + j) (i + j + 1) ((t.f i x).v j (i + j) (by omega) y) +
    (i + 1).negOnePow • (t.f i x).v (j + 1) (i + j + 1) (by omega) (P.d j (j + 1) y) =
    (t.f (i + 1) (Q.d i (i + 1) x)).v j (i + j + 1) (by omega) y at he
  change T.d (i + j) (i + j + 1) ((t.f i x).v j (i + j) (by omega) y) =
    (t.f (i + 1) (Q.d i (i + 1) x)).v j (i + j + 1) (by omega) y +
    i.negOnePow • (t.f i x).v (j + 1) (i + j + 1) (by omega) (P.d j (j + 1) y)
  rw [Int.negOnePow_succ, Units.neg_smul] at he
  exact eq_add_of_sub_eq (by simpa only [sub_eq_add_neg] using he)

/-- 右 tensor の符号なし逆転置。 -/
def uncurryRight (t : Q ⟶ homComplex A P T) : Q ⊗ P ⟶ T :=
  tensorLift (uncurryComponent t) (uncurryComponent_d t)

/-- 逆転置の純粋斉次tensorでの公式。 -/
lemma uncurryRight_apply (t : Q ⟶ homComplex A P T) (i j n : ℤ) (hn : i + j = n)
    (x : Q.X i) (y : P.X j) :
    (uncurryRight t).f n (ιTensorObj Q P i j n hn (x ⊗ₜ[A] y)) =
      (t.f i x).v j n (by omega) y := by
  have hi := ι_tensorLift (uncurryComponent t) (uncurryComponent_d t) i j n hn
  exact congr($(hi).hom (x ⊗ₜ[A] y))

/-- 転置して逆転置すると元の tensor 射を返す。 -/
lemma uncurryRight_curryRight (f : Q ⊗ P ⟶ T) : uncurryRight (curryRight f) = f := by
  apply tensorHom_ext
  intro i j n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (uncurryRight (curryRight f)).f n (ιTensorObj Q P i j n hn (x ⊗ₜ[A] y)) = _
  rw [uncurryRight_apply]
  rfl

/-- 逆転置して転置すると元の Hom 射を返す。 -/
lemma curryRight_uncurryRight (t : Q ⟶ homComplex A P T) : curryRight (uncurryRight t) = t := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro j n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (curryComponent (uncurryRight t) i x).v j n hn y = _
  rw [curryComponent_apply, uncurryRight_apply]

/-- 任意非有界複体の右tensor–Hom同値。 -/
def tensorRightHomEquiv (P Q T : Complex A) : (Q ⊗ P ⟶ T) ≃ (Q ⟶ homComplex A P T) where
  toFun := curryRight
  invFun := uncurryRight
  left_inv := uncurryRight_curryRight
  right_inv := curryRight_uncurryRight
/-- tensor 射の純粋斉次元での公式。 -/
lemma tensorMap_apply {P P' Q Q' : Complex A} (f : P ⟶ P') (g : Q ⟶ Q')
    (i j n : ℤ) (hn : i + j = n) (x : P.X i) (y : Q.X j) :
    (f ⊗ₘ g).f n (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y)) =
      ιTensorObj P' Q' i j n hn (f.f i x ⊗ₜ[A] g.f j y) :=
  SerrePositivity.cochainTensorMap_apply_ι f g i j n hn x y

/-- 右転置は tensor の Q 変数で自然。 -/
lemma curryRight_naturality_source {Q' : Complex A} (g : Q' ⟶ Q) (f : Q ⊗ P ⟶ T) :
    curryRight ((g ⊗ₘ 𝟙 P) ≫ f) = g ≫ curryRight f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (curryComponent ((g ⊗ₘ 𝟙 P) ≫ f) q x).v i j hij y =
    (curryComponent f q (g.f q x)).v i j hij y
  rw [curryComponent_apply, curryComponent_apply]
  change f.f j ((g ⊗ₘ 𝟙 P).f j
    (ιTensorObj Q' P q i j (by omega) (x ⊗ₜ[A] y))) = _
  rw [tensorMap_apply]
  rfl

/-- 右転置は値域 T で自然。 -/
lemma curryRight_naturality_target {T' : Complex A} (f : Q ⊗ P ⟶ T) (g : T ⟶ T') :
    curryRight (f ≫ g) = curryRight f ≫ homPostcompose P g := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (curryComponent (f ≫ g) q x).v i j hij y =
    ((curryComponent f q x).comp (Cochain.ofHom g) (add_zero q)).v i j hij y
  rw [curryComponent_apply, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

/-- 右転置は Hom の原変数 P に反変に自然。 -/
lemma curryRight_naturality_domain {P' : Complex A} (g : P' ⟶ P) (f : Q ⊗ P ⟶ T) :
    curryRight ((𝟙 Q ⊗ₘ g) ≫ f) = curryRight f ≫ homPrecompose g T := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (curryComponent ((𝟙 Q ⊗ₘ g) ≫ f) q x).v i j hij y =
    ((Cochain.ofHom g).comp (curryComponent f q x) (zero_add q)).v i j hij y
  rw [curryComponent_apply, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change f.f j ((𝟙 Q ⊗ₘ g).f j
    (ιTensorObj Q P' q i j (by omega) (x ⊗ₜ[A] y))) =
    (curryComponent f q x).v i j hij (g.f i y)
  rw [tensorMap_apply, curryComponent_apply]
  rfl
end SerrePositivity.DifferentialGraded
end

end Currying

/-! ## Braiding（旧 SerrePositivity/DifferentialGraded/Complexes/Braiding.lean） -/

/-! # 非有界 Ch(A) の Koszul braiding

既存の cochainTensorSymmetry を自然性・hexagon の証明と共に登録する。
-/

@[expose] public section Braiding
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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
      (i * j).negOnePow • ιTensorObj Q P j i n (by omega) (y ⊗ₜ[A] x) :=
  SerrePositivity.cochainTensorSymmetry_hom_apply_ι P Q i j n h x y

/-- signed symmetry は任意の非有界 chain map に関して両変数で自然。 -/
lemma signedSwap_naturality {P P' Q Q' : Complex A} (f : P ⟶ P') (g : Q ⟶ Q') :
    (f ⊗ₘ g) ≫ (signedSwap P' Q').hom = (signedSwap P Q).hom ≫ (g ⊗ₘ f) :=
  SerrePositivity.cochainTensorSymmetry_naturality f g

/-- associator の純粋三重斉次 tensor での公式。 -/
lemma associator_apply (P Q T : Complex A) (i j k n : ℤ) (hn : i + j + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).hom.f n
      (ιTensorObj (P ⊗ Q) T (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      ιTensorObj P (Q ⊗ T) i (j + k) n (by omega)
        (x ⊗ₜ[A] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[A] z)) :=
  SerrePositivity.cochainTensorAssociator_hom_apply_ι P Q T i j k n hn x y z

/-- 中間和次数を別名にしても associator の公式は変わらない。 -/
lemma associator_apply_of_sum (P Q T : Complex A) (i j k l n : ℤ)
    (hl : i + j = l) (hn : l + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).hom.f n
      (ιTensorObj (P ⊗ Q) T l k n hn (ιTensorObj P Q i j l hl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      ιTensorObj P (Q ⊗ T) i (j + k) n (by omega)
        (x ⊗ₜ[A] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[A] z)) :=
  SerrePositivity.cochainTensorAssociator_hom_apply_ι_of_sum P Q T i j k l n hl hn x y z

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
      (signedSwap P Q).hom ▷ T ≫ (α_ Q P T).hom ≫ Q ◁ (signedSwap P T).hom :=
  SerrePositivity.cochainTensorSymmetry_hexagon_forward P Q T

/-- associator の逆を純粋斉次 tensor で評価する。 -/
lemma associator_inv_apply (P Q T : Complex A) (i j k l n : ℤ)
    (hl : j + k = l) (hn : i + l = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).inv.f n
      (ιTensorObj P (Q ⊗ T) i l n hn (x ⊗ₜ[A] ιTensorObj Q T j k l hl (y ⊗ₜ[A] z))) =
      ιTensorObj (P ⊗ Q) T (i + j) k n (by omega)
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z) :=
  SerrePositivity.cochainTensorAssociator_inv_apply_ι_of_sum P Q T i j k l n hl hn x y z

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
      P ◁ (signedSwap Q T).hom ≫ (α_ P T Q).inv ≫ (signedSwap P T).hom ▷ Q :=
  SerrePositivity.cochainTensorSymmetry_hexagon_reverse P Q T

/-- 任意可換環上の非有界複体は Koszul 符号による対称モノイダル圏。 -/
abbrev complexSymmetricCategory : SymmetricCategory (Complex A) :=
  SerrePositivity.cochainTensorSymmetricCategory

/-- 登録した braiding は既存の signed symmetry と同じ同型。 -/
lemma braiding_eq_existing (P Q : Complex A) :
    β_ P Q = SerrePositivity.cochainTensorSymmetry P Q := rfl
end SerrePositivity.DifferentialGraded
end

end Braiding

/-! ## Closed（旧 SerrePositivity/DifferentialGraded/Complexes/Closed.lean） -/

/-! # 非有界 Ch(A) の閉対称モノイダル構造

右 tensor 転置から Koszul braiding を使って Mathlib の左 tensor 随伴を構成する。
右随伴の対象は既存 linearHomComplex のままである。
-/

@[expose] public section Closed
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

/-- 右 tensor と既存線形 Hom 関手の随伴。 -/
def tensorRightHomAdjunction (P : Complex A) : tensorRight P ⊣ homFunctor P :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Q T => tensorRightHomEquiv P Q T
      homEquiv_naturality_left_symm := by
        intro Q' Q T g t
        apply (tensorRightHomEquiv P Q' T).injective
        change curryRight (uncurryRight (g ≫ t)) = curryRight ((g ⊗ₘ 𝟙 P) ≫ uncurryRight t)
        rw [curryRight_naturality_source, curryRight_uncurryRight, curryRight_uncurryRight]
      homEquiv_naturality_right := by
        intro Q T T' f g
        exact curryRight_naturality_target f g }

/-- Mathlib の左 tensor を基準とする閉構造。
同じ Hom 複体を右随伴とし、braiding の自然同型を介して転置する。 -/
instance complexClosed (P : Complex A) : Closed P where
  rightAdj := homFunctor P
  adj := (tensorRightHomAdjunction P).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight P).symm

/-- 任意可換環上の非有界 Ch(A) は閉対称モノイダル圏。 -/
instance complexMonoidalClosed : MonoidalClosed (Complex A) where
  closed := complexClosed

/-- 内部 Hom の対象は既存 linearHomComplex に一致する。 -/
lemma internalHom_eq (P T : Complex A) :
    (ihom P).obj T = homComplex A P T := rfl

/-- 左 tensor の Hom 同値。Mathlib に登録した閉構造そのものを用いる。 -/
abbrev tensorHomEquiv (P Q T : Complex A) : (P ⊗ Q ⟶ T) ≃ (Q ⟶ homComplex A P T) :=
  (ihom.adjunction P).homEquiv Q T
/-- 登録した左tensor転置は、signed braiding の後の右tensor転置に一致する。 -/
lemma tensorHomEquiv_curryRight (P Q T : Complex A) (f : P ⊗ Q ⟶ T) :
    tensorHomEquiv P Q T f = curryRight ((signedSwap Q P).hom ≫ f) := by
  change ((tensorRightHomAdjunction P).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight P).symm).homEquiv Q T f = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  change (tensorRightHomAdjunction P).homEquiv Q T ((β_ P Q).inv ≫ f) = _
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  simp only [tensorRightHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- 左tensor転置の評価公式。全整数次数で Koszul 符号を明示する。 -/
lemma tensorHomEquiv_component (P Q T : Complex A) (f : P ⊗ Q ⟶ T)
    (q i n : ℤ) (hn : i + q = n) (x : Q.X q) (y : P.X i) :
    ((tensorHomEquiv P Q T f).f q x).v i n hn y =
      (q * i).negOnePow • f.f n (HomologicalComplex.ιTensorObj P Q i q n hn (y ⊗ₜ[A] x)) := by
  rw [tensorHomEquiv_curryRight]
  change (curryComponent ((signedSwap Q P).hom ≫ f) q x).v i n hn y = _
  rw [curryComponent_apply]
  change f.f n ((signedSwap Q P).hom.f n
    (HomologicalComplex.ιTensorObj Q P q i n (by omega) (x ⊗ₜ[A] y))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]

/-- 左tensor転置は Q 変数で自然。 -/
lemma tensorHomEquiv_naturality_source (P : Complex A) {Q Q' T : Complex A}
    (g : Q' ⟶ Q) (f : P ⊗ Q ⟶ T) :
    tensorHomEquiv P Q' T ((P ◁ g) ≫ f) = g ≫ tensorHomEquiv P Q T f :=
  (ihom.adjunction P).homEquiv_naturality_left g f

/-- 左tensor転置は T 変数で自然。 -/
lemma tensorHomEquiv_naturality_target (P : Complex A) {Q T T' : Complex A}
    (f : P ⊗ Q ⟶ T) (g : T ⟶ T') :
    tensorHomEquiv P Q T' (f ≫ g) = tensorHomEquiv P Q T f ≫ homPostcompose P g :=
  (ihom.adjunction P).homEquiv_naturality_right f g

/-- 左tensor転置は P 変数で反変に自然。 -/
lemma tensorHomEquiv_naturality_domain {P P' Q T : Complex A}
    (g : P' ⟶ P) (f : P ⊗ Q ⟶ T) :
    tensorHomEquiv P' Q T ((g ▷ Q) ≫ f) = tensorHomEquiv P Q T f ≫ homPrecompose g T := by
  rw [tensorHomEquiv_curryRight, tensorHomEquiv_curryRight]
  change curryRight ((β_ Q P').hom ≫ g ▷ Q ≫ f) = _
  rw [← BraidedCategory.braiding_naturality_right_assoc]
  change curryRight ((𝟙 Q ⊗ₘ g) ≫ (signedSwap Q P).hom ≫ f) = _
  rw [curryRight_naturality_domain]
/-- 左tensorの逆転置は、符号付き交換の後の右tensor逆転置。 -/
lemma tensorHomEquiv_uncurryRight (P Q T : Complex A) (t : Q ⟶ homComplex A P T) :
    (tensorHomEquiv P Q T).symm t = (signedSwap P Q).hom ≫ uncurryRight t := by
  change (((tensorRightHomAdjunction P).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight P).symm).homEquiv Q T).symm t = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  simp only [tensorRightHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- 左tensor逆転置の全次数での成分公式。 -/
lemma tensorHomEquiv_symm_component (P Q T : Complex A) (t : Q ⟶ homComplex A P T)
    (i q n : ℤ) (hn : i + q = n) (y : P.X i) (x : Q.X q) :
    ((tensorHomEquiv P Q T).symm t).f n
      (HomologicalComplex.ιTensorObj P Q i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow • (t.f q x).v i n hn y := by
  rw [tensorHomEquiv_uncurryRight]
  change (uncurryRight t).f n ((signedSwap P Q).hom.f n
    (HomologicalComplex.ιTensorObj P Q i q n hn (y ⊗ₜ[A] x))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [uncurryRight_apply]

/-- Mathlib の evaluation は標準 Hom 評価に Koszul 符号を付けた射。 -/
lemma evaluation_component (P T : Complex A) (i q n : ℤ) (hn : i + q = n)
    (y : P.X i) (f : Homogeneous P T q) :
    ((ihom.ev P).app T).f n
      (HomologicalComplex.ιTensorObj P (homComplex A P T) i q n hn (y ⊗ₜ[A] f)) =
      (i * q).negOnePow • f.v i n hn y := by
  change ((ihom.adjunction P).counit.app T).f n
    (HomologicalComplex.ιTensorObj P (homComplex A P T) i q n hn (y ⊗ₜ[A] f)) = _
  rw [← (ihom.adjunction P).homEquiv_symm_id]
  change ((tensorHomEquiv P (homComplex A P T) T).symm (𝟙 _)).f n _ = _
  rw [tensorHomEquiv_symm_component]
  rfl
/-- 線形 Hom 複体を源に明示した evaluation。 -/
abbrev evaluation (P T : Complex A) : P ⊗ homComplex A P T ⟶ T :=
  (tensorHomEquiv P (homComplex A P T) T).symm (𝟙 _)

/-- 明示した評価は Mathlib の counit と同じ。 -/
lemma evaluation_eq (P T : Complex A) : evaluation P T = (ihom.ev P).app T :=
  (ihom.adjunction P).homEquiv_symm_id T

/-- 明示した評価の斉次成分。 -/
lemma evaluation_apply (P T : Complex A) (i q n : ℤ) (hn : i + q = n)
    (y : P.X i) (f : Homogeneous P T q) :
    (evaluation P T).f n
      (HomologicalComplex.ιTensorObj P (homComplex A P T) i q n hn (y ⊗ₜ[A] f)) =
      (i * q).negOnePow • f.v i n hn y :=
  tensorHomEquiv_symm_component P (homComplex A P T) T (𝟙 _) i q n hn y f
end SerrePositivity.DifferentialGraded
end

end Closed

/-! ## AssociatorReindex（旧 SerrePositivity/DifferentialGraded/Complexes/AssociatorReindex.lean） -/

/-! # 両方の中間和次数を指定するassociatorの成分式 -/

@[expose] public section AssociatorReindex
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

lemma associator_apply_of_sums (P Q T : Complex A) (i j k l m n : ℤ)
    (hl : i + j = l) (hm : j + k = m) (hn : l + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).hom.f n
      (ιTensorObj (P ⊗ Q) T l k n hn (ιTensorObj P Q i j l hl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    ιTensorObj P (Q ⊗ T) i m n (by omega)
      (x ⊗ₜ[A] ιTensorObj Q T j k m hm (y ⊗ₜ[A] z)) := by
  subst l m
  exact associator_apply P Q T i j k n hn x y z

end SerrePositivity.DifferentialGraded
end

end AssociatorReindex

/-! ## CurryingNaturality（旧 SerrePositivity/DifferentialGraded/Complexes/CurryingNaturality.lean） -/

/-! # パラメータ複体の射に関する逆転置と二重転置 -/

@[expose] public section CurryingNaturality
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma uncurryRight_precompose {K L P T : Complex A} (g : L ⟶ K)
    (f : K ⟶ homComplex A P T) :
    uncurryRight (g ≫ f) = (g ▷ P) ≫ uncurryRight f := by
  apply (tensorRightHomEquiv P L T).injective
  change curryRight (uncurryRight (g ≫ f)) = curryRight ((g ⊗ₘ 𝟙 P) ≫ uncurryRight f)
  rw [curryRight_uncurryRight, curryRight_naturality_source, curryRight_uncurryRight]

lemma curryRight_twice_precompose {K L P Q T : Complex A} (g : L ⟶ K)
    (f : (K ⊗ P) ⊗ Q ⟶ T) :
    g ≫ curryRight (curryRight f) = curryRight (curryRight (((g ▷ P) ▷ Q) ≫ f)) := by
  rw [← curryRight_naturality_source, ← curryRight_naturality_source]
  rfl

end SerrePositivity.DifferentialGraded
end

end CurryingNaturality

/-! ## CurryingEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/CurryingEvaluation.lean） -/

/-! # 二重転置の全次数評価式 -/

@[expose] public section CurryingEvaluation
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma curryRight_twice_apply {K P Q T : Complex A} (a : (K ⊗ P) ⊗ Q ⟶ T)
    {k r l s n : ℤ} (hl : r + k = l) (hn : s + l = n)
    (z : K.X k) (m : P.X r) (v : Q.X s) :
    (((curryRight (curryRight a)).f k z).v r l hl m).v s n hn v =
      a.f n (ιTensorObj (K ⊗ P) Q l s n (by omega)
        (ιTensorObj K P k r l (by omega) (z ⊗ₜ[A] m) ⊗ₜ[A] v)) := rfl

lemma curryRight_associator_apply {K P Q S T : Complex A} (i : P ⊗ Q ⟶ S)
    (f : K ⟶ homComplex A S T) {k r l s n : ℤ}
    (hl : r + k = l) (hn : s + l = n) (z : K.X k) (m : P.X r) (v : Q.X s) :
    (((curryRight (curryRight ((α_ K P Q).hom ≫ ((K ◁ i) ≫ uncurryRight f)))).f k z).v
      r l hl m).v s n hn v =
    (f.f k z).v (r + s) n (by omega) (i.f (r + s) (ιTensorObj P Q r s (r + s) rfl
      (m ⊗ₜ[A] v))) := by
  rw [curryRight_twice_apply]
  change (uncurryRight f).f n ((K ◁ i).f n ((α_ K P Q).hom.f n
    (ιTensorObj (K ⊗ P) Q l s n (by omega)
      (ιTensorObj K P k r l (by omega) (z ⊗ₜ[A] m) ⊗ₜ[A] v)))) = _
  rw [associator_apply_of_sums K P Q k r s l (r + s) n (by omega) rfl (by omega),
    whiskerLeft_apply, uncurryRight_apply]

end SerrePositivity.DifferentialGraded
end

end CurryingEvaluation

/-! ## CochainInterchange（旧 SerrePositivity/DifferentialGraded/Complexes/CochainInterchange.lean） -/

/-! # 符号付き交換則を四つのcochainの合成へ運ぶ -/

@[expose] public section CochainInterchange
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma cochain_quad_interchange {X₀ X₁ X₂ X₃ X₄ Y : Complex A} {p q r s n : ℤ}
    (a : Cochain X₀ X₁ p) (b : Cochain X₁ X₂ q) (c : Cochain X₂ X₃ r)
    (d : Cochain X₃ X₄ s) (e : Cochain X₁ Y r) (f : Cochain Y X₃ q)
    (h : e.comp f (by omega : r + q = q + r) = (q * r).negOnePow • b.comp c rfl)
    (hn : p + q + r + s = n) :
    (a.comp b rfl).comp (c.comp d rfl) (by omega : p + q + (r + s) = n) =
      (q * r).negOnePow • (a.comp e rfl).comp (f.comp d rfl)
        (by omega : p + r + (q + s) = n) := by
  have he := congrArg (fun z : Cochain X₁ X₃ (q + r) =>
    a.comp (z.comp d rfl) (by omega : p + (q + r + s) = n)) h
  rw [Cochain.units_smul_comp, Cochain.comp_units_smul] at he
  have he' := congrArg (fun z => (q * r).negOnePow • z) he
  simp only [smul_smul, Int.units_mul_self, one_smul] at he'
  have h₁ : (a.comp b rfl).comp (c.comp d rfl) (by omega : p + q + (r + s) = n) =
      a.comp ((b.comp c rfl).comp d rfl) (by omega : p + (q + r + s) = n) := by
    rw [Cochain.comp_assoc a b (c.comp d rfl) rfl (by omega : q + (r + s) = q + r + s)
      (by omega), ← Cochain.comp_assoc b c d rfl rfl rfl]
  have h₂ : (a.comp e rfl).comp (f.comp d rfl) (by omega : p + r + (q + s) = n) =
      a.comp ((e.comp f (by omega : r + q = q + r)).comp d rfl)
        (by omega : p + (q + r + s) = n) := by
    rw [Cochain.comp_assoc a e (f.comp d rfl) rfl (by omega : r + (q + s) = q + r + s)
      (by omega), ← Cochain.comp_assoc e f d (by omega : r + q = q + r) rfl
        (by omega : r + q + s = q + r + s)]
  exact h₁.trans (he'.symm.trans (congrArg (fun z => (q * r).negOnePow • z) h₂.symm))

end SerrePositivity.DifferentialGraded
end

end CochainInterchange

/-! ## UnitScalarEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/UnitScalarEvaluation.lean） -/

/-! # 複体の射と整数単位スカラー -/

@[expose] public section UnitScalarEvaluation
universe u

namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A]

lemma chain_units_smul {X Y : Complex A} (f : X ⟶ Y) (n : ℤ) (a : ℤˣ) (x : X.X n) :
    f.f n (a • x) = a • f.f n x := by
  simp only [Units.smul_def, map_zsmul]

end SerrePositivity.DifferentialGraded

end UnitScalarEvaluation

/-! ## LowerTruncationSequence（旧 SerrePositivity/DifferentialGraded/Complexes/LowerTruncationSequence.lean） -/

/-! # 下からのstupid truncationの可算列と網羅的余極限 -/

@[expose] public section LowerTruncationSequence
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 下端を小さくする包含の各次数の成分。 -/
def lowerTruncationMapComponent (K : Complex A) (a b : ℤ) (hab : b ≤ a) (q : ℤ) :
    (StupidTruncation.above K a).X q ⟶ (StupidTruncation.above K b).X q :=
  if hq : a ≤ q then
    (StupidTruncation.aboveXIso K a q hq).hom ≫
      (StupidTruncation.aboveXIso K b q (hab.trans hq)).inv
  else 0

lemma lowerTruncationMapComponent_inclusion (K : Complex A) (a b : ℤ) (hab : b ≤ a) (q : ℤ) :
    lowerTruncationMapComponent A K a b hab q ≫ (StupidTruncation.inclusion K b).f q =
      (StupidTruncation.inclusion K a).f q := by
  by_cases hq : a ≤ q
  · simp only [lowerTruncationMapComponent, dite_eq_left hq,
      StupidTruncation.inclusion_f K b q (hab.trans hq),
      StupidTruncation.inclusion_f K a q hq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (StupidTruncation.above_isZero_X K a q (by omega)).eq_of_src _ _

/-- 下端b≤aなら、a以上の切り詰めはb以上の切り詰めへ含まれる。 -/
def lowerTruncationMap (K : Complex A) (a b : ℤ) (hab : b ≤ a) :
    StupidTruncation.above K a ⟶ StupidTruncation.above K b where
  f q := lowerTruncationMapComponent A K a b hab q
  comm' i j _ := by
    apply (cancel_mono ((StupidTruncation.inclusion K b).f j)).1
    rw [Category.assoc, ← (StupidTruncation.inclusion K b).comm,
      ← Category.assoc, lowerTruncationMapComponent_inclusion, Category.assoc,
      lowerTruncationMapComponent_inclusion, (StupidTruncation.inclusion K a).comm]

@[reassoc]
lemma lowerTruncationMap_inclusion (K : Complex A) (a b : ℤ) (hab : b ≤ a) :
    lowerTruncationMap A K a b hab ≫ StupidTruncation.inclusion K b =
      StupidTruncation.inclusion K a := by
  apply Hom.ext
  funext q
  exact lowerTruncationMapComponent_inclusion A K a b hab q

lemma lowerTruncationMap_id (K : Complex A) (a : ℤ) :
    lowerTruncationMap A K a a le_rfl = 𝟙 _ := by
  apply Hom.ext
  funext q
  apply (cancel_mono ((StupidTruncation.inclusion K a).f q)).1
  simpa only [comp_f, id_f, Category.id_comp] using
    congrArg (fun f => f.f q) (lowerTruncationMap_inclusion A K a a le_rfl)

lemma lowerTruncationMap_comp (K : Complex A) (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    lowerTruncationMap A K a b hab ≫ lowerTruncationMap A K b c hbc =
      lowerTruncationMap A K a c (hbc.trans hab) := by
  apply Hom.ext
  funext q
  apply (cancel_mono ((StupidTruncation.inclusion K c).f q)).1
  change (lowerTruncationMap A K a b hab).f q ≫
      (lowerTruncationMap A K b c hbc).f q ≫ (StupidTruncation.inclusion K c).f q = _
  simp only [lowerTruncationMap, lowerTruncationMapComponent_inclusion]

/-- 切り詰め下端を0,−1,−2,…とする可算図式。 -/
def lowerTruncationSequence (K : Complex A) : ℕ ⥤ Complex A where
  obj n := StupidTruncation.above K (-(n : ℤ))
  map {i j} f := lowerTruncationMap A K (-(i : ℤ)) (-(j : ℤ))
    (by have := leOfHom f; omega)
  map_id n := lowerTruncationMap_id A K _
  map_comp f g := (lowerTruncationMap_comp A K _ _ _ _ _).symm

/-- 元の非有界複体への包含の余錐。 -/
def lowerTruncationCocone (K : Complex A) : Cocone (lowerTruncationSequence A K) where
  pt := K
  ι := { app := fun n => StupidTruncation.inclusion K (-(n : ℤ))
         naturality := fun i j f => by
           change lowerTruncationMap A K (-(i : ℤ)) (-(j : ℤ)) _ ≫
             StupidTruncation.inclusion K (-(j : ℤ)) =
               StupidTruncation.inclusion K (-(i : ℤ)) ≫ 𝟙 K
           rw [lowerTruncationMap_inclusion, Category.comp_id] }

/-- 各次数でやがて同型となる包含から、非有界複体を余極限として回復する。 -/
def lowerTruncationCoconeIsColimit (K : Complex A) :
    IsColimit (lowerTruncationCocone A K) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  let F := lowerTruncationSequence A K ⋙ eval (ModuleCat.{u} A) (.up ℤ) q
  let c : Cocone F := (eval (ModuleCat.{u} A) (.up ℤ) q).mapCocone
    (lowerTruncationCocone A K)
  let N := (-q).toNat
  have hN : -(N : ℤ) ≤ q := by dsimp [N]; omega
  have : IsIso (c.ι.app N) := by
    change IsIso ((StupidTruncation.inclusion K (-(N : ℤ))).f q)
    exact StupidTruncation.inclusion_f_isIso K _ q hN
  have hF : F.IsEventuallyConstantFrom N := by
    intro j f
    have hj : -(j : ℤ) ≤ q := by have := leOfHom f; omega
    have : IsIso (c.ι.app j) := by
      change IsIso ((StupidTruncation.inclusion K (-(j : ℤ))).f q)
      exact StupidTruncation.inclusion_f_isIso K _ q hj
    have : IsIso (F.map f ≫ c.ι.app j) := by rw [c.w f]; infer_instance
    exact IsIso.of_isIso_comp_right (F.map f) (c.ι.app j)
  exact hF.isColimitOfIsIso c

/-- 下からの切り詰めの実際の余極限と元の複体との同型。 -/
def lowerTruncationColimitIso (K : Complex A) : colimit (lowerTruncationSequence A K) ≅ K :=
  (colimit.isColimit _).coconePointUniqueUpToIso (lowerTruncationCoconeIsColimit A K)

end SerrePositivity.DifferentialGraded
end

end LowerTruncationSequence

/-! ## MaurerCartanPerturbation（旧 SerrePositivity/DifferentialGraded/Complexes/MaurerCartanPerturbation.lean） -/

/-!
概要：Maurer–Cartan 方程式を満たす次数一 cochain による、非有界複体の微分変更。
方針：元の微分との交換子と追加 cochain の二乗を合わせて二乗零を証明する。
規約：追加 cochain の閉性と二乗零を別々に要求せず、既存の perturbComplex は変更しない。
使われ方：D-8 c2 の coherent dg 図式の全高次成分を含む余極限複体。
-/

@[expose] public section MaurerCartanPerturbation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] (K : Complex R) (θ : Cochain K K 1)

lemma maurerCartanPerturbedDifferential_squared
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) (i : ℤ) :
    (K.d i (i + 1) + θ.v i (i + 1) rfl) ≫
      (K.d (i + 1) (i + 1 + 1) + θ.v (i + 1) (i + 1 + 1) rfl) = 0 := by
  have h := congrArg (fun f : Cochain K K 2 => f.v i (i + 1 + 1) (by omega)) hθ
  rw [Cochain.add_v, δ_v 1 2 (by omega) θ i (i + 1 + 1) (by omega) (i + 1) (i + 1)
    (by omega) rfl, show (2 : ℤ).negOnePow = 1 by decide, one_smul,
    Cochain.comp_v θ θ _ i (i + 1) (i + 1 + 1) rfl rfl, Cochain.zero_v] at h
  rw [add_comp, comp_add, comp_add, K.d_comp_d, zero_add]
  simpa only [add_assoc, add_comm, add_left_comm] using h

def maurerCartanPerturbComplex
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) : Complex R :=
  CochainComplex.of K.X (fun i => K.d i (i + 1) + θ.v i (i + 1) rfl)
    (maurerCartanPerturbedDifferential_squared K θ hθ)

@[simp] lemma maurerCartanPerturbComplex_X
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) (i : ℤ) :
    (maurerCartanPerturbComplex K θ hθ).X i = K.X i := rfl

@[simp] lemma maurerCartanPerturbComplex_d
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) (i : ℤ) :
    (maurerCartanPerturbComplex K θ hθ).d i (i + 1) =
      K.d i (i + 1) + θ.v i (i + 1) rfl :=
  CochainComplex.of_d K.X (fun j => K.d j (j + 1) + θ.v j (j + 1) rfl) i

end SerrePositivity.DifferentialGraded
end

end MaurerCartanPerturbation

/-! ## MaurerCartanHom（旧 SerrePositivity/DifferentialGraded/Complexes/MaurerCartanHom.lean） -/

/-!
概要：両端を Maurer–Cartan 変形した Hom の全次数微分を計算する。
方針：元の微分と二つの追加作用を成分で展開する。
規約：同じ graded cochain と全ての次数・符号を保持する。
使われ方：D-8 c2 の変形加群の作用と余極限比較射の構成。
-/

@[expose] public section MaurerCartanHom
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (θ : Cochain K K 1) (ψ : Cochain L L 1)
  (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
  (hψ : δ 1 2 ψ + ψ.comp ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

def maurerCartanRebaseCochain {p : ℤ} (f : Cochain K L p) :
    Cochain (maurerCartanPerturbComplex K θ hθ) (maurerCartanPerturbComplex L ψ hψ) p :=
  Cochain.mk (fun i j h => f.v i j h)

def maurerCartanForgetCochain {p : ℤ}
    (f : Cochain (maurerCartanPerturbComplex K θ hθ) (maurerCartanPerturbComplex L ψ hψ) p) :
    Cochain K L p := Cochain.mk (fun i j h => f.v i j h)

lemma maurerCartanHom_δ (p : ℤ) (f : Cochain K L p) :
    maurerCartanForgetCochain θ ψ hθ hψ
      (δ p (p + 1) (maurerCartanRebaseCochain θ ψ hθ hψ f)) =
      δ p (p + 1) f + f.comp ψ rfl +
        (p + 1).negOnePow • θ.comp f (by omega : 1 + p = p + 1) := by
  apply Cochain.ext
  intro i j hij
  obtain rfl : j = i + p + 1 := by omega
  simp only [maurerCartanForgetCochain, Cochain.mk_v]
  rw [δ_v (F := maurerCartanPerturbComplex K θ hθ)
    (G := maurerCartanPerturbComplex L ψ hψ) p (p + 1) rfl _
    i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl]
  simp only [maurerCartanRebaseCochain, Cochain.mk_v]
  rw [maurerCartanPerturbComplex_d, maurerCartanPerturbComplex_d]
  simp only [Cochain.add_v, Cochain.units_smul_v]
  rw [δ_v (F := K) (G := L) p (p + 1) rfl f
      i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl,
    Cochain.comp_v f ψ rfl i (i + p) (i + p + 1) rfl rfl,
    Cochain.comp_v θ f _ i (i + 1) (i + p + 1) rfl (by omega)]
  simp only [comp_add, add_comp, smul_add, Units.smul_def, zsmul_comp]
  abel

end SerrePositivity.DifferentialGraded
end

end MaurerCartanHom

/-! ## MaurerCartanHomMap（旧 SerrePositivity/DifferentialGraded/Complexes/MaurerCartanHomMap.lean） -/

/-!
概要：追加微分と可換な全次数 Hom 族を、両端の MC 変形後の Hom 鎖写像へ送る。
方針：元の graded cochain の線形同値と、変形 Hom の微分式を使う。
規約：次数零だけでなく全ての次数と符号付き可換式を保持する。
使われ方：D-8 c2 の変形 dg 加群の全 Hom 作用。
-/

@[expose] public section MaurerCartanHomMap
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (θ : Cochain K K 1) (ψ : Cochain L L 1)
  (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
  (hψ : δ 1 2 ψ + ψ.comp ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

def maurerCartanCochainEquiv (p : ℤ) : Cochain K L p ≃ₗ[R]
    Cochain (maurerCartanPerturbComplex K θ hθ) (maurerCartanPerturbComplex L ψ hψ) p where
  toFun := maurerCartanRebaseCochain θ ψ hθ hψ
  invFun := maurerCartanForgetCochain θ ψ hθ hψ
  left_inv f := by apply Cochain.ext; intro i j h; rfl
  right_inv f := by apply Cochain.ext; intro i j h; rfl
  map_add' f g := by apply Cochain.ext; intro i j h; rfl
  map_smul' a f := by apply Cochain.ext; intro i j h; rfl

def maurerCartanPerturbHomMap (T : Complex R) (f : T ⟶ homComplex R K L)
    (hf : ∀ (p : ℤ) (t : T.X p),
      (f.f p t).comp ψ rfl + (p + 1).negOnePow • θ.comp (f.f p t)
        (by omega : 1 + p = p + 1) = 0) :
    T ⟶ homComplex R (maurerCartanPerturbComplex K θ hθ)
      (maurerCartanPerturbComplex L ψ hψ) :=
  CochainComplex.ofHom
    (fun p => f.f p ≫ ModuleCat.ofHom (maurerCartanCochainEquiv θ ψ hθ hψ p).toLinearMap)
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      apply (maurerCartanCochainEquiv θ ψ hθ hψ (p + 1)).symm.injective
      change maurerCartanForgetCochain θ ψ hθ hψ
        (δ p (p + 1) (maurerCartanRebaseCochain θ ψ hθ hψ (f.f p t))) =
          (f.f (p + 1)) (T.d p (p + 1) t)
      rw [maurerCartanHom_δ, add_assoc, hf p t, add_zero]
      exact ConcreteCategory.congr_hom (f.comm p (p + 1)) t)

end SerrePositivity.DifferentialGraded
end

end MaurerCartanHomMap

/-! ## MaurerCartanTargetHom（旧 SerrePositivity/DifferentialGraded/Complexes/MaurerCartanTargetHom.lean） -/

/-!
概要：標的だけを MC 変形した全次数 Hom の微分を計算する。
方針：元の cochain の成分を保ち、標的微分の追加作用だけを展開する。
規約：始域の複体と全次数を保ち、始域の零変形を別模型として挿入しない。
使われ方：bar の MC 摂動後の終端 HA 成分の比較。
-/

@[expose] public section MaurerCartanTargetHom
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Preadditive HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (ψ : Cochain L L 1)
  (hψ : δ 1 2 ψ + ψ.comp ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

def maurerCartanTargetRebaseCochain {p : ℤ} (f : Cochain K L p) :
    Cochain K (maurerCartanPerturbComplex L ψ hψ) p :=
  Cochain.mk (fun i j hij => f.v i j hij)

def maurerCartanTargetForgetCochain {p : ℤ}
    (f : Cochain K (maurerCartanPerturbComplex L ψ hψ) p) : Cochain K L p :=
  Cochain.mk (fun i j hij => f.v i j hij)

lemma maurerCartanTargetHom_δ (p : ℤ) (f : Cochain K L p) :
    maurerCartanTargetForgetCochain ψ hψ
      (δ p (p + 1) (maurerCartanTargetRebaseCochain ψ hψ f)) =
      δ p (p + 1) f + f.comp ψ rfl := by
  apply Cochain.ext
  intro i j hij
  obtain rfl : j = i + p + 1 := by omega
  simp only [maurerCartanTargetForgetCochain, Cochain.mk_v]
  rw [δ_v (F := K) (G := maurerCartanPerturbComplex L ψ hψ) p (p + 1) rfl _
    i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl]
  simp only [maurerCartanTargetRebaseCochain, Cochain.mk_v]
  rw [maurerCartanPerturbComplex_d]
  simp only [Cochain.add_v]
  rw [δ_v (F := K) (G := L) p (p + 1) rfl f
    i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl,
    Cochain.comp_v f ψ rfl i (i + p) (i + p + 1) rfl rfl]
  simp only [comp_add]
  abel

end SerrePositivity.DifferentialGraded
end

end MaurerCartanTargetHom
