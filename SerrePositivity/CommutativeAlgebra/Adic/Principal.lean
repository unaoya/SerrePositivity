module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # 主元進の完備性

概要：元 `a ∈ R` による `a` 進位相について
- 漸化式の写像 `(x_n) ↦ (x_n - a x_{n+1})` の全射性・単射性と、前完備性・分離性の関係。`a` が正則なら完備性と全単射性は同値。
  `a` はこの写像の核・余核の上で可逆。
- `a` で割った商の上で正則な元 `x` について、`M / x M` も `a` 進完備で `x` は正則。
- 有界な `a` 冪ねじれを持つ加群でも、漸化式の写像から分離性・完備性が出る。
- `a` 進完備な環で `a` について飽和したイデアルは、`a` を法とした生成元で生成される。
方針：`a` 進の合同を一段ずつ持ち上げ、漸化式の解として極限を作る。
規約：完備性は古典的。導来完備化との比較は HomologicalAlgebra の `DerivedCompletion`
（有界ねじれの商は `Adic/BoundedTorsionQuotient`）。
使われ方：導来完備化、局所化の telescope、Bhatt–Scholze 側の prism と perfectoid 環、Fontaine 核の生成元。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicRecurrence

open scoped Pointwise
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 主イデアルの冪による零化近傍への所属は、対応するスカラー冪の像への所属。 -/
theorem mem_principal_pow_smul_top (f : R) (n : ℕ) (x : M) :
    x ∈ (Ideal.span {f}) ^ n • (⊤ : Submodule R M) ↔
      ∃ y : M, (f ^ n) • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- 主イデアルの冪の作用は、任意の直積上で座標ごとに判定できる。 -/
theorem mem_principal_pow_smul_top_function {ι : Type*} (f : R) (n : ℕ) (x : ι → M) :
    x ∈ (Ideal.span {f}) ^ n • (⊤ : Submodule R (ι → M)) ↔
      ∀ i, x i ∈ (Ideal.span {f}) ^ n • (⊤ : Submodule R M) := by
  classical
  simp only [mem_principal_pow_smul_top]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩

/-- 主イデアルに関して完備な加群の任意の直積も完備。 -/
theorem isAdicComplete_function_principal {ι : Type*} (f : R)
    [IsAdicComplete (Ideal.span {f}) M] :
    IsAdicComplete (Ideal.span {f}) (ι → M) := by
  classical
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    funext i
    apply IsHausdorff.haus' (I := Ideal.span {f})
    intro n
    apply SModEq.sub_mem.mpr
    exact (mem_principal_pow_smul_top_function f n _).mp
      (SModEq.sub_mem.mp (hx n)) i
  · intro x hx
    have hcoord (i : ι) : ∃ L : M, ∀ n,
        x n i ≡ L [SMOD ((Ideal.span {f}) ^ n • (⊤ : Submodule R M))] := by
      apply IsPrecomplete.prec'
      intro n m hnm
      apply SModEq.sub_mem.mpr
      exact (mem_principal_pow_smul_top_function f n _).mp
        (SModEq.sub_mem.mp (hx hnm)) i
    choose L hL using hcoord
    refine ⟨L, fun n ↦ ?_⟩
    apply SModEq.sub_mem.mpr
    apply (mem_principal_pow_smul_top_function f n _).mpr
    exact fun i ↦ SModEq.sub_mem.mp (hL i n)

/-- telescopeの双対に現れる列の差分作用。 -/
def adicRecurrenceMap (f : R) : (ℕ → M) →ₗ[R] (ℕ → M) where
  toFun x n := x n - f • x (n + 1)
  map_add' x y := by ext n; simp; abel
  map_smul' r x := by ext n; simp [smul_sub, smul_smul, mul_comm]

/-- 主イデアル進完備性から、列の差分作用の全射性が従う。 -/
theorem adicRecurrenceMap_surjective (f : R)
    [IsAdicComplete (Ideal.span {f}) M] :
    Function.Surjective (adicRecurrenceMap (M := M) f) := by
  let := isAdicComplete_function_principal (M := M) (ι := ℕ) f
  apply surjective_of_mkQ_comp_surjective (I := Ideal.span {f})
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((Ideal.span {f}) • (⊤ : Submodule R (ℕ → M))) y
  refine ⟨x, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change (fun n ↦ x n - f • x (n + 1)) - x ∈ _
  have he : (fun n ↦ x n - f • x (n + 1)) - x = f • (fun n ↦ -x (n + 1)) := by
    funext n
    simp
  rw [he]
  exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top

/-- 分離性から、列の差分作用の単射性が従う。 -/
theorem adicRecurrenceMap_injective (f : R)
    [IsHausdorff (Ideal.span {f}) M] :
    Function.Injective (adicRecurrenceMap (M := M) f) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hstep (n : ℕ) : x n = f • x (n + 1) := by
    have hh := congrFun (LinearMap.mem_ker.mp hx) n
    exact sub_eq_zero.mp hh
  have hpow (k n : ℕ) : x n = f ^ k • x (n + k) := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [pow_succ, mul_smul, ← Nat.add_assoc, ← hstep, ← hk]
  change x = 0
  funext n
  apply IsHausdorff.haus' (I := Ideal.span {f})
  intro k
  apply SModEq.sub_mem.mpr
  simpa only [sub_zero] using
    (mem_principal_pow_smul_top f k (x n)).mpr ⟨x (n + k), (hpow k n).symm⟩

/-- 主イデアル進完備な加群上で、列の差分作用は全単射。 -/
theorem adicRecurrenceMap_bijective (f : R)
    [IsAdicComplete (Ideal.span {f}) M] :
    Function.Bijective (adicRecurrenceMap (M := M) f) :=
  ⟨adicRecurrenceMap_injective f, adicRecurrenceMap_surjective f⟩

/-- 列の差分作用が全射なら、主イデアルに関して前完備。 -/
theorem isPrecomplete_of_adicRecurrenceMap_surjective (f : R)
    (hsurj : Function.Surjective (adicRecurrenceMap (M := M) f)) :
    IsPrecomplete (Ideal.span {f}) M := by
  classical
  constructor
  intro x hx
  have hdiff (n : ℕ) : ∃ b : M, f ^ n • b = x n - x (n + 1) := by
    apply (mem_principal_pow_smul_top f n _).mp
    exact SModEq.sub_mem.mp (hx (Nat.le_succ n))
  choose b hb using hdiff
  obtain ⟨y, hy⟩ := hsurj b
  have hstep (n : ℕ) : y n - f • y (n + 1) = b n := congrFun hy n
  have hconst (n : ℕ) : x n - f ^ n • y n = x 0 - y 0 := by
    induction n with
    | zero => simp
    | succ n hn =>
      have hh : f ^ n • y n - f ^ (n + 1) • y (n + 1) = x n - x (n + 1) := by
        rw [pow_succ, mul_smul, ← smul_sub, hstep, hb]
      calc
        x (n + 1) - f ^ (n + 1) • y (n + 1) = x n - f ^ n • y n := by
          calc
            _ = x (n + 1) - f ^ n • y n +
                (f ^ n • y n - f ^ (n + 1) • y (n + 1)) := by abel
            _ = x (n + 1) - f ^ n • y n + (x n - x (n + 1)) := by rw [hh]
            _ = x n - f ^ n • y n := by abel
        _ = x 0 - y 0 := hn
  refine ⟨x 0 - y 0, fun n ↦ ?_⟩
  apply SModEq.sub_mem.mpr
  apply (mem_principal_pow_smul_top f n _).mpr
  refine ⟨y n, ?_⟩
  rw [← hconst]
  abel

/-- fが非零因子として作用し、差分作用が単射なら、主イデアルに関して分離。 -/
theorem isHausdorff_of_adicRecurrenceMap_injective_of_regular (f : R)
    (hreg : Function.Injective (fun x : M ↦ f • x))
    (hinj : Function.Injective (adicRecurrenceMap (M := M) f)) :
    IsHausdorff (Ideal.span {f}) M := by
  classical
  have hpow (n : ℕ) : Function.Injective (fun x : M ↦ f ^ n • x) := by
    induction n with
    | zero => intro x y hxy; simpa only [pow_zero, one_smul] using hxy
    | succ n hn =>
      intro x y hxy
      apply hreg
      apply hn
      simpa only [pow_succ, mul_smul] using hxy
  constructor
  intro x hx
  have hdiv (n : ℕ) : ∃ y : M, f ^ n • y = x := by
    apply (mem_principal_pow_smul_top f n x).mp
    simpa only [sub_zero] using SModEq.sub_mem.mp (hx n)
  choose y hy using hdiv
  have hstep (n : ℕ) : y n = f • y (n + 1) := by
    apply hpow n
    change f ^ n • y n = f ^ n • (f • y (n + 1))
    rw [hy, ← mul_smul, ← pow_succ, hy]
  have hzero : adicRecurrenceMap f y = 0 := by
    ext n
    exact sub_eq_zero.mpr (hstep n)
  have hyzero : y = 0 := hinj (hzero.trans (map_zero _).symm)
  have h0 := hy 0
  simpa [hyzero] using h0.symm

/-- 非零因子fについて、古典的完備性と列の差分作用の全単射性は同値。 -/
theorem isAdicComplete_iff_adicRecurrenceMap_bijective_of_regular (f : R)
    (hreg : Function.Injective (fun x : M ↦ f • x)) :
    IsAdicComplete (Ideal.span {f}) M ↔
      Function.Bijective (adicRecurrenceMap (M := M) f) := by
  constructor
  · intro h
    let := h
    exact adicRecurrenceMap_bijective f
  · intro h
    let := isHausdorff_of_adicRecurrenceMap_injective_of_regular f hreg h.1
    let := isPrecomplete_of_adicRecurrenceMap_surjective f h.2
    exact ⟨⟩

end AdicRecurrence

section AdicPrincipalKernel

variable {R S : Type*} [CommRing R] [CommRing S]

/-- aで飽和したイデアルは、mod aで生成する一元によって生成される。 -/
theorem ideal_eq_span_of_saturated_of_mod_generator (a : R)
    [IsAdicComplete (Ideal.span {a}) R] (J : Ideal R) (ξ : R) (hξ : ξ ∈ J)
    (hsat : ∀ x : R, a * x ∈ J → x ∈ J)
    (hgen : ∀ x : R, x ∈ J → ∃ r : R, x - ξ * r ∈ Ideal.span {a}) :
    J = Ideal.span {ξ} := by
  let I := Ideal.span {a}
  let f : R →ₗ[R] J := (LinearMap.mulLeft R ξ).codRestrict J
    (fun r ↦ J.mul_mem_right r hξ)
  let := isHausdorff_of_injective_linearMap I J.subtype Subtype.val_injective
  have hf : Function.Surjective f := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R J)) z
    obtain ⟨r, hr⟩ := hgen x x.property
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hr
    have hyJ : y ∈ J := hsat y (by
      rw [← hy]
      exact J.sub_mem x.property (J.mul_mem_right r hξ))
    have hdiff : x - f r ∈ I • (⊤ : Submodule R J) := by
      have he : x - f r = a • (⟨y, hyJ⟩ : J) := by
        apply Subtype.ext
        exact hy
      rw [he]
      exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _))
        (Submodule.mem_top : (⟨y, hyJ⟩ : J) ∈ (⊤ : Submodule R J))
    refine ⟨r, ?_⟩
    apply Eq.symm
    apply (Submodule.Quotient.eq _).mpr
    exact hdiff
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hr⟩ := hf ⟨x, hx⟩
    exact Ideal.mem_span_singleton.mpr ⟨r, (congrArg Subtype.val hr).symm⟩
  · exact (Ideal.span_singleton_le_iff_mem _).mpr hξ

/-- 終域でaが非零因子なら環準同型の核はaで飽和している。 -/
theorem ker_eq_span_of_regular_of_mod_generator (a : R)
    [IsAdicComplete (Ideal.span {a}) R] (f : R →+* S)
    (hregular : Function.Injective (fun x : S ↦ f a * x))
    (ξ : R) (hξ : f ξ = 0)
    (hgen : ∀ x : R, f x = 0 → ∃ r : R, x - ξ * r ∈ Ideal.span {a}) :
    RingHom.ker f = Ideal.span {ξ} := by
  apply ideal_eq_span_of_saturated_of_mod_generator a (RingHom.ker f) ξ hξ
  · intro x hx
    change f (a * x) = 0 at hx
    change f x = 0
    apply hregular
    simpa only [map_mul, mul_zero] using hx
  · exact hgen

end AdicPrincipalKernel

section AdicRecurrenceInversion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Shift a sequence one position to the left. -/
def adicSequenceShift : (ℕ → M) →ₗ[R] (ℕ → M) where
  toFun x n := x (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Shift preserves the kernel of the scalar recurrence. -/
def adicRecurrenceKernelShift (a : R) :
    (adicRecurrenceMap (M := M) a).ker →ₗ[R] (adicRecurrenceMap (M := M) a).ker where
  toFun x := ⟨adicSequenceShift (R := R) x.val, by
    apply LinearMap.mem_ker.mpr
    funext n
    exact congrFun (LinearMap.mem_ker.mp x.property) (n + 1)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by a is invertible on the kernel, with inverse sequence shift. -/
def adicRecurrenceKernelScalarEquiv (a : R) :
    (adicRecurrenceMap (M := M) a).ker ≃ₗ[R] (adicRecurrenceMap (M := M) a).ker where
  toFun x := a • x
  invFun := adicRecurrenceKernelShift a
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (sub_eq_zero.mp (congrFun (LinearMap.mem_ker.mp x.property) n)).symm
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (sub_eq_zero.mp (congrFun (LinearMap.mem_ker.mp x.property) n)).symm
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

/-- Shift descends to the cokernel since it commutes with the recurrence. -/
def adicRecurrenceCokernelShift (a : R) :
    ((ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) →ₗ[R]
      ((ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) :=
  Submodule.mapQ _ _ (adicSequenceShift (R := R)) (by
    rintro x ⟨y, rfl⟩
    exact ⟨adicSequenceShift (R := R) y, rfl⟩)

/-- Modulo the recurrence, scalar multiplication after shift is the identity. -/
lemma adicRecurrenceCokernel_smul_shift (a : R)
    (x : (ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) :
    a • adicRecurrenceCokernelShift (M := M) a x = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change Submodule.Quotient.mk (a • adicSequenceShift (R := R) x) = Submodule.Quotient.mk x
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-x, ?_⟩
    funext n
    simp only [adicRecurrenceMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply,
      Pi.sub_apply, Pi.smul_apply, adicSequenceShift, smul_neg]
    abel

/-- Multiplication by a is also invertible on the cokernel; lim¹ need not vanish. -/
def adicRecurrenceCokernelScalarEquiv (a : R) :
    ((ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) ≃ₗ[R]
      ((ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) where
  toFun x := a • x
  invFun := adicRecurrenceCokernelShift (M := M) a
  left_inv x := by
    rw [map_smul]
    exact adicRecurrenceCokernel_smul_shift (M := M) a x
  right_inv := adicRecurrenceCokernel_smul_shift (M := M) a
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

end AdicRecurrenceInversion

section BoundedTorsion

section AdicRegularQuotient

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]

theorem dvd_of_mul_dvd_of_regular_mod (a g : R)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g))
    (x : R) (hx : a ∣ g * x) : a ∣ x := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hg
  change Ideal.Quotient.mk (Ideal.span {a}) g * Ideal.Quotient.mk (Ideal.span {a}) x =
    Ideal.Quotient.mk (Ideal.span {a}) g * 0
  rw [← map_mul, mul_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hx)

theorem pow_dvd_of_mul_dvd_of_regular_mod (a g : R) (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g))
    (n : ℕ) (x : R) (hx : a ^ n ∣ g * x) : a ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, hy⟩ := dvd_of_mul_dvd_of_regular_mod R a g hg x
      ((dvd_pow_self a (Nat.succ_ne_zero n)).trans hx)
    obtain ⟨z, hz⟩ := hx
    have hcancel : g * y = a ^ n * z := by
      apply ha
      change a * (g * y) = a * (a ^ n * z)
      calc
        _ = g * x := by rw [hy]; ring
        _ = a ^ (n + 1) * z := hz
        _ = _ := by rw [pow_succ]; ring
    obtain ⟨w, hw⟩ := ih y ⟨z, hcancel⟩
    exact ⟨w, by rw [hy, hw, pow_succ]; ring⟩

theorem isSMulRegular_quotient_span_of_regular_mod (a g : R) (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g)) :
    IsSMulRegular (R ⧸ Ideal.span {g}) (Ideal.Quotient.mk (Ideal.span {g}) a) := by
  change IsSMulRegular (R ⧸ Ideal.span {g}) (algebraMap R (R ⧸ Ideal.span {g}) a)
  rw [isSMulRegular_algebraMap_iff]
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {g}) a).mpr
  intro x hx
  change a * x ∈ Ideal.span {g} at hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨z, hz⟩ := dvd_of_mul_dvd_of_regular_mod R a g hg y ⟨x, hy.symm⟩
  apply Ideal.mem_span_singleton.mpr
  refine ⟨z, ?_⟩
  apply ha
  change a * x = a * (g * z)
  rw [hy, hz]
  ring

theorem isAdicComplete_quotient_span_of_regular_mod (a g : R)
    [IsAdicComplete (Ideal.span {a}) R] (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g)) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a}) (R ⧸ Ideal.span {g}) := by
  let f := LinearMap.mulLeft R g
  have hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f ((Ideal.span {a}) ^ (n + k) • (⊤ : Submodule R R)) ≤
        (Ideal.span {a}) ^ n • (⊤ : Submodule R R) := by
    refine ⟨0, fun n x hx ↦ ?_⟩
    simp only [Submodule.mem_comap, f, LinearMap.mulLeft_apply, Nat.add_zero,
      Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    exact pow_dvd_of_mul_dvd_of_regular_mod R a g ha hg n x hx
  have hrange : f.range = (Ideal.span {g} : Submodule R R) := by
    ext x
    simp only [LinearMap.mem_range, f, LinearMap.mulLeft_apply, Ideal.mem_span_singleton, dvd_def]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩
  let : IsAdicComplete (Ideal.span {a}) (R ⧸ Ideal.span {g}) := by
    rw [← hrange]
    exact isAdicComplete_quotient_range_of_uniform_filtration_bound (Ideal.span {a}) f hbound
  have hmap : (Ideal.span {a}).map (algebraMap R (R ⧸ Ideal.span {g})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

end AdicRegularQuotient

section AdicBoundedTorsion

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有界なf冪ねじれの下では、差分作用の単射性からf進分離性が従う。 -/
theorem isHausdorff_of_adicRecurrenceMap_injective_of_bounded_torsion (f : R)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0)
    (hinj : Function.Injective (adicRecurrenceMap (M := M) f)) :
    IsHausdorff (Ideal.span {f}) M := by
  classical
  obtain ⟨N, hN⟩ := hbounded
  constructor
  intro x hx
  have hdiv (n : ℕ) : ∃ y : M, f ^ n • y = x := by
    apply (mem_principal_pow_smul_top f n x).mp
    simpa only [sub_zero] using SModEq.sub_mem.mp (hx n)
  choose y hy using hdiv
  let z : ℕ → M := fun n ↦ f ^ N • y (n + N)
  have hstep (n : ℕ) : z n = f • z (n + 1) := by
    have herr : f ^ (n + N) • (y (n + N) - f • y (n + 1 + N)) = 0 := by
      rw [smul_sub, ← mul_smul, ← pow_succ, hy]
      have he : n + N + 1 = n + 1 + N := by omega
      rw [he, hy, sub_self]
    have h := hN (n + N) _ herr
    dsimp only [z]
    rw [smul_sub, smul_smul, mul_comm (f ^ N) f, ← smul_smul] at h
    exact sub_eq_zero.mp h
  have hz : adicRecurrenceMap f z = 0 := by
    ext n
    exact sub_eq_zero.mpr (hstep n)
  have hzero : z = 0 := hinj (hz.trans (map_zero _).symm)
  have hxz : z 0 = x := by simpa only [z, zero_add] using hy N
  rw [hzero] at hxz
  exact hxz.symm

/-- 有界ねじれの下で、差分作用の全単射性から古典的完備性が従う。 -/
theorem isAdicComplete_of_adicRecurrenceMap_bijective_of_bounded_torsion (f : R)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0)
    (hbij : Function.Bijective (adicRecurrenceMap (M := M) f)) :
    IsAdicComplete (Ideal.span {f}) M := by
  let := isHausdorff_of_adicRecurrenceMap_injective_of_bounded_torsion f hbounded hbij.1
  let := isPrecomplete_of_adicRecurrenceMap_surjective f hbij.2
  exact ⟨⟩

end AdicBoundedTorsion

end BoundedTorsion

end SerrePositivity
