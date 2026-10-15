module
public import SerrePositivity.DifferentialGraded.Complexes.HomFunctor
public import SerrePositivity.DifferentialGraded.Complexes.Composition
public import SerrePositivity.DifferentialGraded.Complexes.Monoidal
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous

/-! # 非有界 tensor と線形 Hom の転置

最初に Q⊗P → T と Q → linearHomComplex(P,T) の符号なし転置を構成する。
微分の符号は tensor 第一因子の Q 次数に一致する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
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
