module

public import Mathlib.RingTheory.DividedPowers.DPMorphism

/-!
# 基底の分冪と両立する分冪包

## 概要
Berthelot I.2.3.1 の相対分冪包を、入力環と同じ宇宙で構成する。

## 方針
環の式とイデアル内の式を分ける。すべての相対分冪代数で同じ値を取る
環の式を同一視し、イデアル内の式の像に分冪を入れる。

## 規約
分冪の演算はイデアル内の式にだけ適用する。正次数の分冪は再び
イデアル内の式になる。零次の分冪は環の単位元で与える。

## 使われ方
p 完備な相対分冪包と枠の分冪 Čech 脈体の構成。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 基底の分冪と両立する分冪包の普遍性。Berthelot I.2.3.1。 -/
structure IsRelativePDEnvelope {k : Type u} [CommRing k] {J : Ideal k}
    (γ : DividedPowers J) {B : Type u} [CommRing B] [Algebra k B] (K : Ideal B)
    {D : Type u} [CommRing D] [Algebra k D] {I : Ideal D} (δ : DividedPowers I)
    (η : B →ₐ[k] D) : Prop where
  /-- 入力イデアルは分冪イデアルに入る。 -/
  map_le : K.map η ≤ I
  /-- 係数射は分冪を保つ。 -/
  base_dp : DividedPowers.IsDPMorphism γ δ (algebraMap k D)
  /-- 分冪を保つ延長の存在と一意性。 -/
  lift : ∀ {E : Type u} [CommRing E] [Algebra k E] {L : Ideal E} (ε : DividedPowers L)
    (g : B →ₐ[k] E), K.map g ≤ L →
      DividedPowers.IsDPMorphism γ ε (algebraMap k E) →
      ∃! h : D →ₐ[k] E, DividedPowers.IsDPMorphism δ ε h.toRingHom ∧ h.comp η = g

namespace RelativePDEnvelope

variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
variable {J : Ideal k}

private structure Target (γ : DividedPowers J) (K : Ideal B) where
  carrier : Type u
  [ring : CommRing carrier]
  [algebra : Algebra k carrier]
  ideal : Ideal carrier
  dividedPowers : DividedPowers ideal
  input : B →ₐ[k] carrier
  input_le : K.map input ≤ ideal
  base_dp : DividedPowers.IsDPMorphism γ dividedPowers (algebraMap k carrier)

attribute [local instance] Target.ring Target.algebra

private inductive Term (K : Ideal B) : Bool → Type u
  | const (x : B) : Term K false
  | gen (x : K) : Term K true
  | ofIdeal (x : Term K true) : Term K false
  | add {i} (x y : Term K i) : Term K i
  | neg {i} (x : Term K i) : Term K i
  | mul {i} (x : Term K false) (y : Term K i) : Term K i
  | pow (x : Term K false) (n : ℕ) : Term K false
  | dp (n : ℕ) (x : Term K true) : Term K true

variable {γ : DividedPowers J} {K : Ideal B}

private def Term.eval (T : Target γ K) : {i : Bool} → Term K i → T.carrier
  | _, .const x => T.input x
  | _, .gen x => T.input x
  | _, .ofIdeal x => x.eval T
  | _, .add x y => x.eval T + y.eval T
  | _, .neg x => -x.eval T
  | _, .mul x y => x.eval T * y.eval T
  | _, .pow x n => x.eval T ^ n
  | _, .dp n x => T.dividedPowers.dpow (n + 1) (x.eval T)

private theorem Term.eval_mem (T : Target γ K) :
    (x : Term K true) → x.eval T ∈ T.ideal
  | .gen x => T.input_le (Ideal.mem_map_of_mem _ x.property)
  | .add x y => T.ideal.add_mem (x.eval_mem T) (y.eval_mem T)
  | .neg x => T.ideal.neg_mem (x.eval_mem T)
  | .mul x y => T.ideal.mul_mem_left (x.eval T) (y.eval_mem T)
  | .dp n x => T.dividedPowers.dpow_mem (Nat.succ_ne_zero n) (x.eval_mem T)

private def termSetoid (γ : DividedPowers J) (K : Ideal B) : Setoid (Term K false) where
  r x y := ∀ T : Target γ K, x.eval T = y.eval T
  iseqv := ⟨fun _ _ => rfl, fun h T => (h T).symm, fun h₁ h₂ T => (h₁ T).trans (h₂ T)⟩

/-- 相対分冪包の台環。有限式の商なので入力と同じ宇宙に属する。 -/
def Ring (γ : DividedPowers J) (K : Ideal B) : Type u := Quotient (termSetoid γ K)

private abbrev cls (x : Term K false) : Ring γ K := Quotient.mk _ x

private def project (T : Target γ K) : Ring γ K → T.carrier :=
  Quotient.lift (Term.eval T) (fun _ _ h => h T)

private theorem project_ext {x y : Ring γ K} (h : ∀ T : Target γ K, project T x = project T y) :
    x = y := Quotient.inductionOn₂ x y (fun _ _ h => Quotient.sound h) h

private instance : Zero (Ring γ K) := ⟨cls (.const 0)⟩
private instance : One (Ring γ K) := ⟨cls (.const 1)⟩
private instance : NatCast (Ring γ K) := ⟨fun n => cls (.const n)⟩
private instance : IntCast (Ring γ K) := ⟨fun n => cls (.const n)⟩

private instance : Add (Ring γ K) :=
  ⟨Quotient.map₂ Term.add fun _ _ h _ _ h' T => congrArg₂ (· + ·) (h T) (h' T)⟩

private instance : Neg (Ring γ K) :=
  ⟨Quotient.map Term.neg fun _ _ h T => congrArg Neg.neg (h T)⟩

private instance : Mul (Ring γ K) :=
  ⟨Quotient.map₂ Term.mul fun _ _ h _ _ h' T => congrArg₂ (· * ·) (h T) (h' T)⟩

private instance : Sub (Ring γ K) := ⟨fun x y => x + -y⟩
private instance : SMul ℕ (Ring γ K) := ⟨fun n x => (n : Ring γ K) * x⟩
private instance : SMul ℤ (Ring γ K) := ⟨fun n x => (n : Ring γ K) * x⟩

private instance : Pow (Ring γ K) ℕ :=
  ⟨fun x n => Quotient.map (sa := termSetoid γ K) (sb := termSetoid γ K)
    (fun a => Term.pow a n) (fun _ _ h T => congrArg (· ^ n) (h T)) x⟩

private theorem project_add (T : Target γ K) (x y : Ring γ K) :
    project T (x + y) = project T x + project T y :=
  Quotient.inductionOn₂ x y (fun _ _ => rfl)

private theorem project_neg (T : Target γ K) (x : Ring γ K) :
    project T (-x) = -project T x := Quotient.inductionOn x (fun _ => rfl)

private theorem project_mul (T : Target γ K) (x y : Ring γ K) :
    project T (x * y) = project T x * project T y :=
  Quotient.inductionOn₂ x y (fun _ _ => rfl)

private theorem project_pow (T : Target γ K) (x : Ring γ K) (n : ℕ) :
    project T (x ^ n) = project T x ^ n := Quotient.inductionOn x (fun _ => rfl)

private theorem project_natCast (T : Target γ K) (n : ℕ) :
    project T (n : Ring γ K) = n := map_natCast T.input n

private theorem project_intCast (T : Target γ K) (n : ℤ) :
    project T (n : Ring γ K) = n := map_intCast T.input n

@[no_expose] instance : CommRing (Ring γ K) :=
  Function.Injective.commRing (fun x (T : Target γ K) => project T x)
    (fun _ _ h => project_ext (congrFun h))
    (funext fun T => map_zero T.input)
    (funext fun T => map_one T.input)
    (fun x y => funext fun T => project_add T x y)
    (fun x y => funext fun T => project_mul T x y)
    (fun x => funext fun T => project_neg T x)
    (fun x y => funext fun T => by
      change project T (x + -y) = project T x - project T y
      rw [project_add, project_neg, sub_eq_add_neg])
    (fun n x => funext fun T => by
      change project T ((n : Ring γ K) * x) = n • project T x
      rw [project_mul, project_natCast, nsmul_eq_mul])
    (fun n x => funext fun T => by
      change project T ((n : Ring γ K) * x) = n • project T x
      rw [project_mul, project_intCast, zsmul_eq_mul])
    (fun x n => funext fun T => project_pow T x n)
    (fun n => funext fun T => project_natCast T n)
    (fun n => funext fun T => project_intCast T n)

private def projection (T : Target γ K) : Ring γ K →+* T.carrier where
  toFun := project T
  map_zero' := map_zero T.input
  map_one' := map_one T.input
  map_add' := project_add T
  map_mul' := project_mul T

/-- 入力環から分冪包への標準環射。 -/
def unitRingHom (γ : DividedPowers J) (K : Ideal B) : B →+* Ring γ K where
  toFun x := cls (.const x)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := project_ext fun T => map_add T.input _ _
  map_mul' _ _ := project_ext fun T => map_mul T.input _ _

@[no_expose] instance : Algebra k (Ring γ K) :=
  ((unitRingHom γ K).comp (algebraMap k B)).toAlgebra

/-- 入力環から分冪包への基底つきの標準射。 -/
def unit (γ : DividedPowers J) (K : Ideal B) : B →ₐ[k] Ring γ K :=
  ⟨unitRingHom γ K, fun _ => rfl⟩

/-- イデアル内の式が表す分冪包のイデアル。 -/
def ideal (γ : DividedPowers J) (K : Ideal B) : Ideal (Ring γ K) where
  carrier := Set.range (fun x : Term K true => (cls (.ofIdeal x) : Ring γ K))
  zero_mem' := ⟨.gen ⟨0, K.zero_mem⟩, project_ext fun _ => rfl⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨.add x y, project_ext fun _ => rfl⟩
  smul_mem' := by
    intro r z hz
    refine Quotient.inductionOn r (fun a => ?_)
    obtain ⟨x, rfl⟩ := hz
    exact ⟨.mul a x, project_ext fun _ => rfl⟩

private theorem projection_mem (T : Target γ K) {x : Ring γ K} (hx : x ∈ ideal γ K) :
    projection T x ∈ T.ideal := by
  obtain ⟨t, rfl⟩ := hx
  exact t.eval_mem T

private theorem cls_ideal (t : Term K true) : (cls (.ofIdeal t) : Ring γ K) ∈ ideal γ K :=
  ⟨t, rfl⟩

private def dpow (n : ℕ) (x : Ring γ K) : Ring γ K := by
  classical
  exact if hx : x ∈ ideal γ K then
    match n with
    | 0 => 1
    | n + 1 => cls (.ofIdeal (.dp n (Exists.choose hx)))
  else 0

private theorem projection_dpow (T : Target γ K) (n : ℕ) {x : Ring γ K}
    (hx : x ∈ ideal γ K) :
    projection T (dpow n x) = T.dividedPowers.dpow n (projection T x) := by
  classical
  unfold dpow
  rw [dite_eq_left hx]
  cases n with
  | zero => rw [map_one, T.dividedPowers.dpow_zero (projection_mem T hx)]
  | succ n =>
    change T.dividedPowers.dpow (n + 1) (Term.eval T (Exists.choose hx)) = _
    rw [show Term.eval T (Exists.choose hx) = projection T x from
      congrArg (projection T) (Exists.choose_spec hx)]

/-- 分冪包の分冪。各標的への評価で分冪の公理を確かめる。 -/
def dividedPowers (γ : DividedPowers J) (K : Ideal B) : DividedPowers (ideal γ K) where
  dpow := dpow
  dpow_null hx := by classical exact dite_eq_right hx
  dpow_zero hx := by classical exact dite_eq_left hx
  dpow_one hx := project_ext fun T => by
    change projection T (dpow 1 _) = _
    rw [projection_dpow T 1 hx, T.dividedPowers.dpow_one (projection_mem T hx)]
    rfl
  dpow_mem := by
    intro n x hn hx
    classical
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
      unfold dpow
      rw [dite_eq_left hx]
      exact cls_ideal _
  dpow_add {n x y} hx hy := project_ext fun T => by
    change projection T (dpow n (x + y)) = projection T _
    rw [projection_dpow T n ((ideal γ K).add_mem hx hy), map_add, map_sum,
      T.dividedPowers.dpow_add (projection_mem T hx) (projection_mem T hy)]
    simp only [map_mul, projection_dpow T _ hx, projection_dpow T _ hy]
  dpow_mul {n a x} hx := project_ext fun T => by
    change projection T (dpow n (a * x)) = projection T _
    rw [projection_dpow T n ((ideal γ K).mul_mem_left a hx), map_mul, map_mul, map_pow,
      projection_dpow T n hx, T.dividedPowers.dpow_mul (projection_mem T hx)]
  mul_dpow {m n x} hx := project_ext fun T => by
    change projection T (dpow m x * dpow n x) = projection T _
    rw [map_mul, map_mul, map_natCast, projection_dpow T m hx, projection_dpow T n hx,
      projection_dpow T (m + n) hx, T.dividedPowers.mul_dpow (projection_mem T hx)]
  dpow_comp {m n x} hn hx := project_ext fun T => by
    have hd : dpow n x ∈ ideal γ K := by
      classical
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
        unfold dpow
        rw [dite_eq_left hx]
        exact cls_ideal _
    change projection T (dpow m (dpow n x)) = projection T _
    rw [projection_dpow T m hd, projection_dpow T n hx, map_mul, map_natCast,
      projection_dpow T (m * n) hx, T.dividedPowers.dpow_comp hn (projection_mem T hx)]

private theorem dpow_cls_succ (n : ℕ) (t : Term K true) :
    (dividedPowers γ K).dpow (n + 1) (cls (.ofIdeal t)) = cls (.ofIdeal (.dp n t)) :=
  project_ext fun T => projection_dpow T (n + 1) (cls_ideal t)

private theorem unit_mem {x : B} (hx : x ∈ K) : unit γ K x ∈ ideal γ K :=
  ⟨.gen ⟨x, hx⟩, project_ext fun _ => rfl⟩

private def liftTo (T : Target γ K) : Ring γ K →ₐ[k] T.carrier :=
  ⟨projection T, T.input.commutes⟩

private theorem liftTo_isDPMorphism (T : Target γ K) :
    DividedPowers.IsDPMorphism (dividedPowers γ K) T.dividedPowers (liftTo T).toRingHom :=
  ⟨Ideal.map_le_iff_le_comap.mpr (fun _ hx => projection_mem T hx),
    fun _ hx => (projection_dpow T _ hx).symm⟩

private theorem liftTo_unique (T : Target γ K) {h : Ring γ K →ₐ[k] T.carrier}
    (hh : DividedPowers.IsDPMorphism (dividedPowers γ K) T.dividedPowers h.toRingHom)
    (hc : h.comp (unit γ K) = T.input) : h = liftTo T := by
  let represent : {i : Bool} → Term K i → Ring γ K
    | false, t => cls t
    | true, t => cls (.ofIdeal t)
  have hconst (x : B) : h (cls (.const x)) = T.input x :=
    DFunLike.congr_fun hc x
  have hAdd {i} (x y : Term K i) : represent (.add x y) = represent x + represent y := by
    cases i <;> exact project_ext fun _ => rfl
  have hNeg {i} (x : Term K i) : represent (.neg x) = -represent x := by
    cases i <;> exact project_ext fun _ => rfl
  have hMul {i} (x : Term K false) (y : Term K i) :
      represent (.mul x y) = represent x * represent y := by
    cases i <;> exact project_ext fun _ => rfl
  have he : ∀ {i : Bool} (t : Term K i), h (represent t) = t.eval T := by
    intro i t
    induction t with
    | const x => exact hconst x
    | gen x =>
      change h (cls (.ofIdeal (.gen x))) = T.input x
      rw [← hconst x]
      exact congrArg h (project_ext fun _ => rfl)
    | ofIdeal t ht => exact ht
    | add x y hx hy =>
      rw [hAdd, map_add, hx, hy]
      rfl
    | neg x hx =>
      rw [hNeg, map_neg, hx]
      rfl
    | mul x y hx hy =>
      rw [hMul, map_mul, hx, hy]
      rfl
    | pow x n hx =>
      change h (represent x ^ n) = _
      rw [map_pow, hx]
      rfl
    | dp n x hx =>
      change h (cls (.ofIdeal (.dp n x))) = _
      rw [← dpow_cls_succ n x]
      exact (hh.map_dpow (cls_ideal x)).trans
        (congrArg (T.dividedPowers.dpow (n + 1)) hx)
  ext x
  exact Quotient.inductionOn x (fun t => he t)

/-- 構成した分冪包は基底の分冪と両立し、分冪を保つ延長の普遍性を持つ。 -/
theorem isRelativePDEnvelope (hK : J.map (algebraMap k B) ≤ K) :
    IsRelativePDEnvelope γ K (dividedPowers γ K) (unit γ K) where
  map_le := Ideal.map_le_iff_le_comap.mpr (fun _ hx => unit_mem hx)
  base_dp := by
    have hmem : ∀ x ∈ J, algebraMap k (Ring γ K) x ∈ ideal γ K :=
      fun x hx => unit_mem (hK (Ideal.mem_map_of_mem _ hx))
    refine ⟨Ideal.map_le_iff_le_comap.mpr hmem, fun {n} x hx => ?_⟩
    apply project_ext
    intro T
    change projection T (dpow n (algebraMap k (Ring γ K) x)) =
      T.input (algebraMap k B (γ.dpow n x))
    rw [projection_dpow T n (hmem x hx)]
    change T.dividedPowers.dpow n (T.input (algebraMap k B x)) = _
    rw [T.input.commutes, T.input.commutes]
    exact T.base_dp.dpow_comp x hx
  lift ε g hg he := by
    let T : Target γ K := {
      carrier := _
      ideal := _
      dividedPowers := ε
      input := g
      input_le := hg
      base_dp := he }
    exact ⟨liftTo T, ⟨liftTo_isDPMorphism T, rfl⟩,
      fun _ hh => liftTo_unique T hh.1 hh.2⟩

end RelativePDEnvelope

end SerrePositivity.BhattScholze.Prismatic
