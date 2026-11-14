module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.DeRham.Graded
public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz

/-!
# 多項式 de Rham 代数の普遍性

## 概要
次数 0 と 1 の写像を、積と微分に両立する写像へ一意に延ばす。

## 方針
標的の次数付き直和を η⁰ 経由の係数代数とし、外積代数の普遍性を使う。
微分との両立と一意性は、多項式と定係数 1 形式からの生成で示す。

## 使われ方
Hodge–Tate 写像の外積への延長（BS 著者版 Construction 4.9）。
-/

noncomputable section

universe u

open scoped DirectSum TensorProduct

namespace SerrePositivity.DeRham

variable {k T : Type u} [CommRing k] [Fintype T] [DecidableEq T]
variable (H : GradedCommDGAlgebra k)

private theorem of_cast (i j : ℕ) (h : i = j) (x : H.carrier i) :
    DirectSum.of H.carrier j (cast (congrArg H.carrier h) x) =
      DirectSum.of H.carrier i x := by
  subst j
  rfl

private theorem ofZero_mul_comm (a : H.carrier 0) (b : ⨁ i, H.carrier i) :
    DirectSum.ofZeroRingHom H.carrier a * b = b * DirectSum.ofZeroRingHom H.carrier a := by
  induction b using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [mul_add, add_mul, hx, hy]
  | of j b =>
    change DirectSum.of H.carrier 0 a * DirectSum.of H.carrier j b =
      DirectSum.of H.carrier j b * DirectSum.of H.carrier 0 a
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
    have h := H.mul_comm a b
    simp only [Nat.zero_mul, pow_zero, one_zsmul] at h
    rw [← h]
    exact (of_cast H _ _ (Nat.add_comm 0 j) _).symm

variable (η0 : Poly k T →+* H.carrier 0)

@[instance_reducible] private def inducedAlgebra : Algebra k (⨁ i, H.carrier i) :=
  ((DirectSum.ofZeroRingHom H.carrier).comp (η0.comp MvPolynomial.C)).toAlgebra'
    (fun c b => ofZero_mul_comm H (η0 (MvPolynomial.C c)) b)

variable (η1 : forms k T 1 →+ H.carrier 1)
variable (hlin : ∀ (f : Poly k T) (ω : forms k T 1), η1 (f • ω) = η0 f • η1 ω)
variable (hsq : ∀ ω : forms k T 1, H.mul (η1 ω) (η1 ω) = 0)

private def constantOneForm : (T → k) →ₗ[k] forms k T 1 :=
  (TensorProduct.mk k (Poly k T) (⋀[k]^1 (T → k)) 1).comp
    (exteriorPower.oneEquiv k (T → k)).symm.toLinearMap

private theorem constantOneForm_smul (c : k) (v : T → k) :
    constantOneForm (c • v) = (MvPolynomial.C c : Poly k T) • constantOneForm v := by
  change (1 : Poly k T) ⊗ₜ[k] ((exteriorPower.oneEquiv k (T → k)).symm (c • v)) =
    MvPolynomial.C c • ((1 : Poly k T) ⊗ₜ[k] ((exteriorPower.oneEquiv k (T → k)).symm v))
  rw [map_smul, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  simp [Algebra.smul_def]

include η1 hlin in
private def exteriorGenerators :
    let := inducedAlgebra H η0
    let := (inducedAlgebra H η0).toModule
    (T → k) →ₗ[k] (⨁ i, H.carrier i) := by
  let := inducedAlgebra H η0
  let : Module k (⨁ i, H.carrier i) := (inducedAlgebra H η0).toModule
  refine ⟨(DirectSum.of H.carrier 1).comp (η1.comp constantOneForm.toAddMonoidHom), ?_⟩
  intro c v
  change DirectSum.of H.carrier 1 (η1 (constantOneForm (c • v))) = _
  rw [constantOneForm_smul, hlin, DirectSum.of_zero_smul]
  rfl

include hsq in
private theorem exteriorGenerators_sq (v : T → k) :
    exteriorGenerators H η0 η1 hlin v * exteriorGenerators H η0 η1 hlin v = 0 := by
  change DirectSum.of H.carrier 1 (η1 (constantOneForm v)) *
    DirectSum.of H.carrier 1 (η1 (constantOneForm v)) = 0
  rw [DirectSum.of_mul_of]
  change DirectSum.of H.carrier (1 + 1) (H.mul (η1 (constantOneForm v))
    (η1 (constantOneForm v))) = 0
  rw [hsq, map_zero]

include η1 hlin hsq in
private def exteriorLift :
    let := inducedAlgebra H η0
    ExteriorAlgebra k (T → k) →ₐ[k] (⨁ i, H.carrier i) := by
  let := inducedAlgebra H η0
  exact ExteriorAlgebra.lift k ⟨exteriorGenerators H η0 η1 hlin,
    exteriorGenerators_sq H η0 η1 hlin hsq⟩

include η1 hlin hsq in
private theorem exteriorLift_ι (v : T → k) :
    exteriorLift H η0 η1 hlin hsq (ExteriorAlgebra.ι k v) =
      DirectSum.of H.carrier 1 (η1 (constantOneForm v)) := by
  unfold exteriorLift
  rw [ExteriorAlgebra.lift_ι_apply]
  rfl

include η1 hlin hsq in
private theorem exteriorLift_ιMulti (n : ℕ) (v : Fin n → (T → k)) :
    ∃ y, exteriorLift H η0 η1 hlin hsq (ExteriorAlgebra.ιMulti k n v) =
      DirectSum.of H.carrier n y := by
  induction n with
  | zero =>
    refine ⟨1, ?_⟩
    rw [ExteriorAlgebra.ιMulti_zero_apply, map_one, DirectSum.of_zero_one]
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (Matrix.vecTail v)
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, exteriorLift_ι, hy, DirectSum.of_mul_of]
    refine ⟨cast (congrArg H.carrier (Nat.add_comm 1 n))
      (H.mul (η1 (constantOneForm (v 0))) y), ?_⟩
    exact (of_cast H _ _ (Nat.add_comm 1 n) _).symm

include η1 hlin hsq in
private theorem exteriorLift_homogeneous (n : ℕ) (ω : ⋀[k]^n (T → k)) :
    ∃ y, exteriorLift H η0 η1 hlin hsq ω = DirectSum.of H.carrier n y := by
  let := inducedAlgebra H η0
  let : Module k (⨁ i, H.carrier i) := (inducedAlgebra H η0).toModule
  let f := exteriorLift H η0 η1 hlin hsq
  have hω : ω ∈ Submodule.span k (Set.range (exteriorPower.ιMulti k n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact exteriorLift_ιMulti H η0 η1 hlin hsq n v
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    change f ((x : ExteriorAlgebra k (T → k)) + y) = _
    rw [map_add, ha, hb, map_add]
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨η0 (MvPolynomial.C c) • a, ?_⟩
    change f (c • (x : ExteriorAlgebra k (T → k))) = _
    rw [Algebra.smul_def, map_mul, f.commutes, ha, DirectSum.of_zero_smul]
    rfl

private def coefficientMap :
    let := inducedAlgebra H η0
    Poly k T →ₐ[k] (⨁ i, H.carrier i) := by
  let := inducedAlgebra H η0
  exact { (DirectSum.ofZeroRingHom H.carrier).comp η0 with
    commutes' := fun _ => rfl }

include η1 hlin hsq in
private def liftOnForms (n : ℕ) :
    let := inducedAlgebra H η0
    let := (inducedAlgebra H η0).toModule
    forms k T n →ₗ[k] (⨁ i, H.carrier i) := by
  let := inducedAlgebra H η0
  let : Module k (⨁ i, H.carrier i) := (inducedAlgebra H η0).toModule
  let F := (exteriorLift H η0 η1 hlin hsq).toLinearMap.comp
    (⋀[k]^n (T → k)).subtype
  exact TensorProduct.lift (((LinearMap.mul k (⨁ i, H.carrier i)).compl₂ F).comp
    (coefficientMap H η0).toLinearMap)

include η1 hlin hsq in
private theorem liftOnForms_tmul (n : ℕ) (f : Poly k T) (ω : ⋀[k]^n (T → k)) :
    liftOnForms H η0 η1 hlin hsq n (f ⊗ₜ[k] ω) =
      DirectSum.of H.carrier 0 (η0 f) * exteriorLift H η0 η1 hlin hsq ω := by
  let := inducedAlgebra H η0
  let : Module k (⨁ i, H.carrier i) := (inducedAlgebra H η0).toModule
  rw [liftOnForms, TensorProduct.lift.tmul]
  rfl

include η1 hlin hsq in
private theorem liftOnForms_homogeneous (n : ℕ) (ω : forms k T n) :
    ∃ y, liftOnForms H η0 η1 hlin hsq n ω = DirectSum.of H.carrier n y := by
  induction ω using TensorProduct.inductionOn with
  | tmul f ω =>
    obtain ⟨y, hy⟩ := exteriorLift_homogeneous H η0 η1 hlin hsq n ω
    refine ⟨η0 f • y, ?_⟩
    rw [liftOnForms_tmul, hy, DirectSum.of_zero_smul]
  | add ω ω' h h' =>
    obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ := h'
    exact ⟨x + y, by rw [map_add, hx, hy, map_add]⟩

include η1 hlin hsq in
private def gradedLift (n : ℕ) : forms k T n →+ H.carrier n :=
  (DirectSum.component k ℕ H.carrier n).toAddMonoidHom.comp
    (liftOnForms H η0 η1 hlin hsq n).toAddMonoidHom

include η1 hlin hsq in
private theorem of_gradedLift (n : ℕ) (ω : forms k T n) :
    DirectSum.of H.carrier n (gradedLift H η0 η1 hlin hsq n ω) =
      liftOnForms H η0 η1 hlin hsq n ω := by
  obtain ⟨y, hy⟩ := liftOnForms_homogeneous H η0 η1 hlin hsq n ω
  unfold gradedLift
  change DirectSum.of H.carrier n
    (DirectSum.component k ℕ H.carrier n (liftOnForms H η0 η1 hlin hsq n ω)) = _
  rw [hy]
  congr 1
  exact DirectSum.component.lof_self k (M := H.carrier) n y

private theorem wedge_tmul' {i j : ℕ} (f g : Poly k T)
    (a : ⋀[k]^i (T → k)) (b : ⋀[k]^j (T → k)) :
    wedge k T (f ⊗ₜ[k] a) (g ⊗ₜ[k] b) =
      (f * g) ⊗ₜ[k] exteriorWedge k (T → k) i j a b := by
  rw [wedge, TensorProduct.map₂_apply_tmul, TensorProduct.map_tmul]
  rfl

include η1 hlin hsq in
private theorem liftOnForms_wedge {i j : ℕ} (a : forms k T i) (b : forms k T j) :
    liftOnForms H η0 η1 hlin hsq (i + j) (wedge k T a b) =
      liftOnForms H η0 η1 hlin hsq i a * liftOnForms H η0 η1 hlin hsq j b := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [wedge, map_add, LinearMap.add_apply, add_mul] at ha hb ⊢
    rw [ha, hb]
  | tmul f a =>
    induction b using TensorProduct.inductionOn with
    | add b c hb hc =>
      simp only [wedge, map_add, mul_add] at hb hc ⊢
      rw [hb, hc]
    | tmul g b =>
      rw [wedge_tmul', liftOnForms_tmul, liftOnForms_tmul, liftOnForms_tmul, map_mul,
        DirectSum.of_zero_mul]
      let F := exteriorLift H η0 η1 hlin hsq
      have he : F (exteriorWedge k (T → k) i j a b) = F a * F b := F.map_mul a b
      rw [he]
      calc
        _ = DirectSum.of H.carrier 0 (η0 f) *
            (DirectSum.of H.carrier 0 (η0 g) * F a) * F b := by
          simp only [mul_assoc]
        _ = DirectSum.of H.carrier 0 (η0 f) *
            (F a * DirectSum.of H.carrier 0 (η0 g)) * F b := by
          have hc := ofZero_mul_comm H (η0 g) (F a)
          change DirectSum.of H.carrier 0 (η0 g) * F a =
            F a * DirectSum.of H.carrier 0 (η0 g) at hc
          rw [hc]
        _ = _ := by simp only [mul_assoc]; rfl

include η1 hlin hsq in
private theorem gradedLift_wedge {i j : ℕ} (a : forms k T i) (b : forms k T j) :
    gradedLift H η0 η1 hlin hsq (i + j) (wedge k T a b) =
      H.mul (gradedLift H η0 η1 hlin hsq i a) (gradedLift H η0 η1 hlin hsq j b) := by
  apply DirectSum.of_injective (β := H.carrier) (i + j)
  rw [of_gradedLift]
  change _ = DirectSum.of H.carrier (i + j)
    (GradedMonoid.GMul.mul (gradedLift H η0 η1 hlin hsq i a)
      (gradedLift H η0 η1 hlin hsq j b))
  rw [← DirectSum.of_mul_of, of_gradedLift, of_gradedLift]
  exact liftOnForms_wedge H η0 η1 hlin hsq a b

private theorem formsZeroEquiv_tmul (f : Poly k T) :
    formsZeroEquiv k T f =
      f ⊗ₜ[k] (exteriorPower.zeroEquiv k (T → k)).symm 1 := by
  simp [formsZeroEquiv]

omit [Fintype T] [DecidableEq T] in
private theorem exteriorZero_one :
    ((exteriorPower.zeroEquiv k (T → k)).symm 1 : ExteriorAlgebra k (T → k)) = 1 := by
  simp [exteriorPower.zeroEquiv_symm_apply, ExteriorAlgebra.ιMulti_zero_apply]

include η1 hlin hsq in
private theorem gradedLift_zero (f : Poly k T) :
    gradedLift H η0 η1 hlin hsq 0 (formsZeroEquiv k T f) = η0 f := by
  apply DirectSum.of_injective (β := H.carrier) 0
  rw [of_gradedLift, formsZeroEquiv_tmul, liftOnForms_tmul, exteriorZero_one, map_one, mul_one]

include η1 hlin hsq in
private theorem gradedLift_one (ω : forms k T 1) :
    gradedLift H η0 η1 hlin hsq 1 ω = η1 ω := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul f a =>
    let v := exteriorPower.oneEquiv k (T → k) a
    have ha : a = (exteriorPower.oneEquiv k (T → k)).symm v := by simp [v]
    have hcoe : a.val = ExteriorAlgebra.ι k v := by
      rw [ha]
      simp [exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply]
    apply DirectSum.of_injective (β := H.carrier) 1
    rw [of_gradedLift, liftOnForms_tmul, hcoe, exteriorLift_ι, ← DirectSum.of_zero_smul]
    have ht : f ⊗ₜ[k] a = f • constantOneForm v := by
      change f ⊗ₜ[k] a =
        f • (1 ⊗ₜ[k] (exteriorPower.oneEquiv k (T → k)).symm v)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← ha]
    rw [ht, hlin]

private theorem cast_tmul {i j : ℕ} (h : i = j) (f : Poly k T)
    (a : ⋀[k]^i (T → k)) :
    cast (congrArg (forms k T) h) (f ⊗ₜ[k] a) =
      f ⊗ₜ[k] cast (congrArg (fun n => ↥(⋀[k]^n (T → k))) h) a := by
  subst j
  rfl

omit [Fintype T] [DecidableEq T] in
private theorem cast_exterior_val {i j : ℕ} (h : i = j) (a : ⋀[k]^i (T → k)) :
    ((cast (congrArg (fun n => ↥(⋀[k]^n (T → k))) h) a :
      ⋀[k]^j (T → k)) : ExteriorAlgebra k (T → k)) = a := by
  subst j
  rfl

private theorem forms_induction
    {P : ∀ i, forms k T i → Prop}
    (hz : ∀ i, P i 0)
    (ha : ∀ i a b, P i a → P i b → P i (a + b))
    (h₀ : ∀ f, P 0 (formsZeroEquiv k T f))
    (h₁ : ∀ v, P 1 (constantOneForm v))
    (hm : ∀ {i j} a b, P i a → P j b → P (i + j) (wedge k T a b))
    (i : ℕ) (a : forms k T i) : P i a := by
  have hcast {i j : ℕ} (h : i = j) {a : forms k T i} (ha : P i a) :
      P j (cast (congrArg (forms k T) h) a) := by
    subst j
    exact ha
  have hgen (n : ℕ) (v : Fin n → T → k) (f : Poly k T) :
      P n (f ⊗ₜ[k] exteriorPower.ιMulti k n v) := by
    induction n with
    | zero =>
      have h : exteriorPower.ιMulti k 0 v =
          (exteriorPower.zeroEquiv k (T → k)).symm 1 := by
        apply Subtype.ext
        rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply, exteriorZero_one]
      rw [h, ← formsZeroEquiv_tmul]
      exact h₀ f
    | succ n ih =>
      let a := (exteriorPower.oneEquiv k (T → k)).symm (v 0)
      let b := exteriorPower.ιMulti k n (Matrix.vecTail v)
      have h := hcast (Nat.add_comm 1 n) (hm (constantOneForm (v 0)) (f ⊗ₜ[k] b)
        (h₁ _) (ih (Matrix.vecTail v)))
      change P (n + 1) (cast (congrArg (forms k T) (Nat.add_comm 1 n))
        (wedge k T ((1 : Poly k T) ⊗ₜ[k] a) (f ⊗ₜ[k] b))) at h
      have he : cast (congrArg (fun q => ↥(⋀[k]^q (T → k))) (Nat.add_comm 1 n))
          (exteriorWedge k (T → k) 1 n a b) = exteriorPower.ιMulti k (n + 1) v := by
        apply Subtype.ext
        rw [cast_exterior_val (Nat.add_comm 1 n)]
        simp [a, b, exteriorWedge, exteriorPower.oneEquiv_symm_apply,
          ExteriorAlgebra.ιMulti_succ_apply (n := n), ExteriorAlgebra.ιMulti_apply (n := 1)]
      rwa [wedge_tmul', one_mul, cast_tmul (Nat.add_comm 1 n), he] at h
  have htmul (a : ⋀[k]^i (T → k)) : ∀ f : Poly k T, P i (f ⊗ₜ[k] a) := by
    have h : a ∈ Submodule.span k (Set.range (exteriorPower.ιMulti k i)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      exact hgen i v
    | zero => intro f; rw [TensorProduct.tmul_zero]; exact hz i
    | add a b _ _ ha' hb' =>
      intro f
      rw [TensorProduct.tmul_add]
      exact ha i _ _ (ha' f) (hb' f)
    | smul c a _ h =>
      intro f
      rw [← TensorProduct.smul_tmul]
      exact h _
  induction a using TensorProduct.inductionOn with
  | tmul f a => exact htmul a f
  | add a b h h' => exact ha i _ _ h h'

private def linearPolynomial (v : T → k) : Poly k T :=
  ∑ t : T, MvPolynomial.C (v t) * MvPolynomial.X t

private theorem pderiv_linearPolynomial (v : T → k) (t : T) :
    MvPolynomial.pderiv t (linearPolynomial v) = MvPolynomial.C (v t) := by
  rw [linearPolynomial, map_sum, Finset.sum_eq_single t]
  · rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self, mul_one]
  · intro j _ hj
    rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hj, mul_zero]
  · simp

private theorem deRhamD_linearPolynomial (v : T → k) :
    deRhamD k T 0 (formsZeroEquiv k T (linearPolynomial v)) = constantOneForm v := by
  rw [formsZeroEquiv_tmul]
  simp only [deRhamD, deRhamDLinear, LinearMap.toAddMonoidHom_coe, LinearMap.sum_apply,
    TensorProduct.map_tmul]
  change (∑ t : T, MvPolynomial.pderiv t (linearPolynomial v) ⊗ₜ[k]
    wedgeOne k (T → k) 0 ((exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1))
      ((exteriorPower.zeroEquiv k (T → k)).symm 1)) = _
  simp only [pderiv_linearPolynomial]
  have hW (t : T) :
      wedgeOne k (T → k) 0
        ((exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1))
        ((exteriorPower.zeroEquiv k (T → k)).symm 1) =
          (exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1) := by
    apply Subtype.ext
    rw [wedgeOne_coe, exteriorZero_one, mul_one]
  simp only [hW]
  have hterm (t : T) :
      MvPolynomial.C (v t) ⊗ₜ[k] (exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1) =
        constantOneForm ((v t) • Pi.single t 1) := by
    rw [constantOneForm_smul]
    change _ = MvPolynomial.C (v t) • ((1 : Poly k T) ⊗ₜ[k] _)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  simp only [hterm, ← map_sum]
  congr 1
  ext t
  simp [Pi.smul_apply, Pi.single_apply]

private theorem degreeCast_apply {i j : ℕ} (h : i = j)
    (Φ : ∀ n, forms k T n →+ H.carrier n) (a : forms k T i) :
    Φ j (cast (congrArg (forms k T) h) a) = cast (congrArg H.carrier h) (Φ i a) := by
  subst j
  rfl

include η1 hlin hsq in
private theorem gradedLift_d
    (hd : ∀ f : Poly k T, η1 (deRhamD k T 0 (formsZeroEquiv k T f)) = H.d 0 (η0 f))
    (i : ℕ) (a : forms k T i) :
    gradedLift H η0 η1 hlin hsq (i + 1) (deRhamD k T i a) =
      H.d i (gradedLift H η0 η1 hlin hsq i a) := by
  let Φ := gradedLift H η0 η1 hlin hsq
  apply forms_induction (P := fun i a => Φ (i + 1) (deRhamD k T i a) = H.d i (Φ i a))
  · intro i
    simp
  · intro i a b ha hb
    simp only [map_add]
    rw [ha, hb]
  · intro f
    change gradedLift H η0 η1 hlin hsq 1 (deRhamD k T 0 (formsZeroEquiv k T f)) =
      H.d 0 (gradedLift H η0 η1 hlin hsq 0 (formsZeroEquiv k T f))
    rw [gradedLift_one, gradedLift_zero, hd]
  · intro v
    change gradedLift H η0 η1 hlin hsq 2 (deRhamD k T 1 (constantOneForm v)) =
      H.d 1 (gradedLift H η0 η1 hlin hsq 1 (constantOneForm v))
    rw [gradedLift_one, ← deRhamD_linearPolynomial, deRhamD_comp, hd, H.d_sq, map_zero]
  · intro i j a b ha hb
    have hm {i j : ℕ} (a : forms k T i) (b : forms k T j) :
        Φ (i + j) (wedge k T a b) = H.mul (Φ i a) (Φ j b) :=
      gradedLift_wedge H η0 η1 hlin hsq a b
    have hm' : Φ ((i + j) + 1) (wedge k T (i := i) (j := j + 1) a (deRhamD k T j b)) =
        H.mul (Φ i a) (Φ (j + 1) (deRhamD k T j b)) := hm a (deRhamD k T j b)
    rw [deRhamD_wedge, map_add, map_zsmul,
      degreeCast_apply H (by omega : (i + 1) + j = (i + j) + 1), hm, hm, hm', ha, hb]
    exact (H.leibniz (Φ i a) (Φ j b)).symm

/-- 概要：次数 0 と 1 の写像が平方零と微分の条件を満たせば、
多項式 de Rham 代数の射に一意に延びる（BS 著者版 Construction 4.9 で使う普遍性）。
方針：外積代数の普遍性で斉次写像を作り、微分との両立を生成元と Leibniz 則で示す。
規約：次数 1 の線形性は次数 0 の写像を経由し、次数 0 は `formsZeroEquiv` で比較する。
使われ方：Hodge–Tate 写像の外積への延長。 -/
public theorem exists_unique_dgHom (k : Type u) [CommRing k] (T : Type u)
    [Fintype T] [DecidableEq T] (H : GradedCommDGAlgebra k)
    (η0 : Poly k T →+* H.carrier 0) (η1 : forms k T 1 →+ H.carrier 1)
    (hlin : ∀ (f : Poly k T) (ω : forms k T 1), η1 (f • ω) = η0 f • η1 ω)
    (hd : ∀ f : Poly k T, η1 (deRhamD k T 0 (formsZeroEquiv k T f)) = H.d 0 (η0 f))
    (hsq : ∀ ω : forms k T 1, H.mul (η1 ω) (η1 ω) = 0) :
    ∃! Φ : ∀ i, forms k T i →+ H.carrier i,
      (∀ f, Φ 0 (formsZeroEquiv k T f) = η0 f) ∧ (∀ ω, Φ 1 ω = η1 ω) ∧
      (∀ {i j} (ω : forms k T i) (η : forms k T j),
        Φ (i + j) (wedge k T ω η) = H.mul (Φ i ω) (Φ j η)) ∧
      (∀ i ω, Φ (i + 1) (deRhamD k T i ω) = H.d i (Φ i ω)) := by
  let Φ := gradedLift H η0 η1 hlin hsq
  refine ⟨Φ, ⟨gradedLift_zero H η0 η1 hlin hsq, gradedLift_one H η0 η1 hlin hsq,
    gradedLift_wedge H η0 η1 hlin hsq, gradedLift_d H η0 η1 hlin hsq hd⟩, ?_⟩
  intro Ψ hΨ
  funext i
  apply AddMonoidHom.ext
  intro a
  apply forms_induction (P := fun i a => Ψ i a = Φ i a)
  · intro i
    simp
  · intro i a b ha hb
    simp only [map_add, ha, hb]
  · intro f
    exact (hΨ.1 f).trans (gradedLift_zero H η0 η1 hlin hsq f).symm
  · intro v
    exact (hΨ.2.1 _).trans (gradedLift_one H η0 η1 hlin hsq _).symm
  · intro i j a b ha hb
    rw [hΨ.2.2.1, ha, hb]
    exact (gradedLift_wedge H η0 η1 hlin hsq a b).symm

end SerrePositivity.DeRham

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.9" (partial := special) "多項式代数の場合の Hodge–Tate 写像（BS-D68 停止点 3）。一般の R は不要 ／ 11-10 更新（2）"] _root_.SerrePositivity.DeRham.exists_unique_dgHom
