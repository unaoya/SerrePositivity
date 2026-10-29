module

public import SerrePositivity.FieldTheory.FrobeniusPowerSubfield
public import SerrePositivity.FieldTheory.PMonomialSpan
public import SerrePositivity.FieldTheory.PBasis
public import Mathlib.RingTheory.AdicCompletion.Basic
public import SerrePositivity.CommutativeAlgebra.FrobeniusKernelLift
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Algebra.Operations

/-! # 冪零核に沿う p 基底の持ち上げ

概要：標数 `p` の環の全射 `f : A → k`（`k` は体）の核の元を `x ↦ x^{p^n}` が消すとする。`k` の p 基底 `b` と、
その持ち上げ `β`（`f (β_i) = b_i`）を任意に指定すると、`f` の切断 `k → A` で `b_i ↦ β_i` となるものが
一意に存在する（`IsPBasis.liftOfFrobeniusKernel`）。特に核が冪零ならよい。
一意性は、核が分離的（`IsHausdorff`）なら全射性なしで成り立つ。
方針：Frobenius 冪を降ろして係数写像 `c : k^{p^n} → A` を作る（`frobeniusCoefficientLift`）。`k` は `k^{p^n}` 上
`bᵈ`（`d_i < p^n`）を基底に持つ（`FrobeniusPowerSubfield`）ので、`bᵈ ↦ βᵈ` で `k^{p^n}` 線形写像を定め、
単項式の積の繰り上がり（`pMonomial_mul_frobeniusCarry`）から乗法性を確かめる。一意性は、二つの切断が
`b` と全ての `p^n` 乗で一致すること（`IsPBasis.ringHom_ext_of_eq_pow_exp`）から。
規約：完全体性・有限 p 次数・Noether 性・局所性は仮定しない。
使われ方：完備な核に沿う持ち上げと係数体（`CoefficientField`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section CoefficientLift

variable {A : Type*} [CommRing A]
variable (p : ℕ) [Fact p.Prime] [CharP A p]

variable {k : Type*} [Field k] [CharP k p]

/-- p^n 乗部分体からの実際の係数写像。任意の剰余体に適用できる。 -/
noncomputable def frobeniusCoefficientLift (f : A →+* k) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) :
    frobeniusPowerSubfield k p n →+* A :=
  (liftFrobeniusOfSurjective p f hf n hkill).comp
    (frobeniusPowerEquiv k p n).symm.toRingHom

/-- 係数写像は剰余体への包含写像を実際に持ち上げる。 -/
theorem map_frobeniusCoefficientLift (f : A →+* k) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0)
    (c : frobeniusPowerSubfield k p n) :
    f (frobeniusCoefficientLift p f hf n hkill c) = c := by
  change f (liftFrobeniusOfSurjective p f hf n hkill ((frobeniusPowerEquiv k p n).symm c)) = c
  rw [map_liftFrobeniusOfSurjective]
  exact congrArg Subtype.val ((frobeniusPowerEquiv k p n).apply_symm_apply c)

/-- 剰余体の元の任意の持ち上げについて、その p^n 乗は係数写像の値と一致する。 -/
theorem frobeniusCoefficientLift_pow (f : A →+* k) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) (x : A) :
    frobeniusCoefficientLift p f hf n hkill (frobeniusPowerEquiv k p n (f x)) = x ^ p ^ n := by
  change liftFrobeniusOfSurjective p f hf n hkill
    ((frobeniusPowerEquiv k p n).symm (frobeniusPowerEquiv k p n (f x))) = _
  rw [RingEquiv.symm_apply_apply, liftFrobeniusOfSurjective_apply_map]

end CoefficientLift

section Carry

variable {k A ι : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime] [CharP k p]
  (n : ℕ) (b : ι → k) (β : ι → A) (c : frobeniusPowerSubfield k p n →+* A)
  (hβ : ∀ i, β i ^ p ^ n = c (frobeniusPowerEquiv k p n (b i)))

include hβ

/-- 生成元の冪関係は、すべての有限台単項式の冪関係を与える。 -/
theorem map_frobenius_finsuppMonomial (d : ι →₀ ℕ) :
    c (frobeniusPowerEquiv k p n (d.prod (fun i m ↦ b i ^ m))) =
      (d.prod (fun i m ↦ β i ^ m)) ^ p ^ n := by
  rw [map_finsuppProd, map_finsuppProd]
  simp only [map_pow, ← hβ, Finsupp.prod, ← Finset.prod_pow, ← pow_mul]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.mul_comm]

/-- 指数の和を p^n で割り、繰り上がりを係数写像の値へ移す。 -/
theorem pMonomial_mul_frobeniusCarry (d e : PExponent (p ^ n) ι) :
    pMonomial β d * pMonomial β e =
      c (frobeniusPowerEquiv k p n
        ((d.val + e.val).prod (fun i m ↦ b i ^ (m / p ^ n)))) *
          pMonomial β (PExponent.remainder (p ^ n) (d.val + e.val)) := by
  have hc := map_frobenius_finsuppMonomial n b β c hβ
    ((d.val + e.val).mapRange (fun m ↦ m / p ^ n) (Nat.zero_div _))
  rw [Finsupp.prod_mapRange_index (fun i ↦ pow_zero (b i)),
    Finsupp.prod_mapRange_index (fun i ↦ pow_zero (β i))] at hc
  rw [hc]
  rw [pMonomial, pMonomial,
    ← Finsupp.prod_add_index' (by intro i; simp) (by intro i a m; exact pow_add _ _ _)]
  exact finsuppMonomial_eq_pow_mul_remainder (p ^ n) β (d.val + e.val)

end Carry

section RingHom

variable {k A ι : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime] [CharP k p]
  {b : ι → k}

/-- 係数写像 `c` に沿って、単項式基底 `bᵈ`（`d_i < p^n`）を `βᵈ` へ送る線形写像。 -/
def IsPBasis.frobeniusMonomialConstr (hb : IsPBasis k p b) (n : ℕ)
    (c : frobeniusPowerSubfield k p n →+* A) (β : ι → A) :
    letI : Algebra (frobeniusPowerSubfield k p n) A := c.toAlgebra
    k →ₗ[frobeniusPowerSubfield k p n] A :=
  letI : Algebra (frobeniusPowerSubfield k p n) A := c.toAlgebra
  (hb.frobeniusMonomialBasis n).constr (frobeniusPowerSubfield k p n) (pMonomial β)

theorem IsPBasis.frobeniusMonomialConstr_pMonomial (hb : IsPBasis k p b) (n : ℕ)
    (c : frobeniusPowerSubfield k p n →+* A) (β : ι → A) (d : PExponent (p ^ n) ι) :
    hb.frobeniusMonomialConstr n c β (pMonomial b d) = pMonomial β d := by
  let : Algebra (frobeniusPowerSubfield k p n) A := c.toAlgebra
  unfold IsPBasis.frobeniusMonomialConstr
  simpa only [hb.frobeniusMonomialBasis_apply] using
    (hb.frobeniusMonomialBasis n).constr_basis (frobeniusPowerSubfield k p n) (pMonomial β) d

theorem IsPBasis.frobeniusMonomialConstr_one (hb : IsPBasis k p b) (n : ℕ)
    (c : frobeniusPowerSubfield k p n →+* A) (β : ι → A) :
    hb.frobeniusMonomialConstr n c β 1 = 1 := by
  simpa using hb.frobeniusMonomialConstr_pMonomial n c β 0

theorem IsPBasis.frobeniusMonomialConstr_coe (hb : IsPBasis k p b) (n : ℕ)
    (c : frobeniusPowerSubfield k p n →+* A) (β : ι → A) (a : frobeniusPowerSubfield k p n) :
    hb.frobeniusMonomialConstr n c β (a : k) = c a := by
  let : Algebra (frobeniusPowerSubfield k p n) A := c.toAlgebra
  have h := (hb.frobeniusMonomialConstr n c β).map_smul a (1 : k)
  simp only [Algebra.smul_def] at h
  change hb.frobeniusMonomialConstr n c β ((a : k) * 1) =
    c a * hb.frobeniusMonomialConstr n c β 1 at h
  simpa only [hb.frobeniusMonomialConstr_one, mul_one] using h

/-- 冪関係 `β_i^{p^n} = c(b_i^{p^n})` を満たす `β` から作る環準同型 `k → A`。係数 `k^{p^n}` の上では `c`、
単項式は `bᵈ ↦ βᵈ`。乗法性は繰り上がり公式を基底の上で確かめ、双線形写像の外延性で全体へ延ばす。 -/
def IsPBasis.ringHomOfFrobeniusRelations (hb : IsPBasis k p b) (n : ℕ)
    (c : frobeniusPowerSubfield k p n →+* A) (β : ι → A)
    (hβ : ∀ i, β i ^ p ^ n = c (frobeniusPowerEquiv k p n (b i))) : k →+* A where
  toFun := hb.frobeniusMonomialConstr n c β
  map_one' := hb.frobeniusMonomialConstr_one n c β
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := by
    let F := frobeniusPowerSubfield k p n
    let : Algebra F A := c.toAlgebra
    let L := hb.frobeniusMonomialConstr n c β
    let B := hb.frobeniusMonomialBasis n
    have hL := hb.frobeniusMonomialConstr_pMonomial n c β
    have hm : ∀ d e : PExponent (p ^ n) ι,
        L (pMonomial b d * pMonomial b e) = L (pMonomial b d) * L (pMonomial b e) := by
      intro d e
      let a : F := frobeniusPowerEquiv k p n
        ((d.val + e.val).prod (fun i m ↦ b i ^ (m / p ^ n)))
      let r := PExponent.remainder (p ^ n) (d.val + e.val)
      have hs := pMonomial_mul_frobeniusCarry n b b F.subtype (fun _ ↦ rfl) d e
      rw [hs, hL, hL]
      change L (a • pMonomial b r) = pMonomial β d * pMonomial β e
      rw [L.map_smul, hL]
      change c a * pMonomial β r = pMonomial β d * pMonomial β e
      exact (pMonomial_mul_frobeniusCarry n b β c hβ d e).symm
    have hmul : (LinearMap.mul F k).compr₂ L = (LinearMap.mul F A).compl₁₂ L L := by
      apply LinearMap.ext_basis B B
      intro d e
      change L (B d * B e) = L (B d) * L (B e)
      simpa only [B, hb.frobeniusMonomialBasis_apply] using hm d e
    intro x y
    exact congrArg (fun g : k →ₗ[F] k →ₗ[F] A ↦ g x y) hmul

variable (hb : IsPBasis k p b) (n : ℕ) (c : frobeniusPowerSubfield k p n →+* A) (β : ι → A)
  (hβ : ∀ i, β i ^ p ^ n = c (frobeniusPowerEquiv k p n (b i)))

@[simp] theorem IsPBasis.ringHomOfFrobeniusRelations_coe (a : frobeniusPowerSubfield k p n) :
    hb.ringHomOfFrobeniusRelations n c β hβ (a : k) = c a :=
  hb.frobeniusMonomialConstr_coe n c β a

@[simp] theorem IsPBasis.ringHomOfFrobeniusRelations_pMonomial (d : PExponent (p ^ n) ι) :
    hb.ringHomOfFrobeniusRelations n c β hβ (pMonomial b d) = pMonomial β d :=
  hb.frobeniusMonomialConstr_pMonomial n c β d

/-- 指定した p 基底の元は `β` へ送られる。`n = 0` も含む。 -/
@[simp] theorem IsPBasis.ringHomOfFrobeniusRelations_apply (i : ι) :
    hb.ringHomOfFrobeniusRelations n c β hβ (b i) = β i := by
  cases n with
  | zero =>
    have h := hb.ringHomOfFrobeniusRelations_coe 0 c β hβ (frobeniusPowerEquiv k p 0 (b i))
    simpa using h.trans (hβ i).symm
  | succ n =>
    have hq : 1 < p ^ (n + 1) := Nat.one_lt_pow (Nat.succ_ne_zero n) (Fact.out : p.Prime).one_lt
    simpa using hb.ringHomOfFrobeniusRelations_pMonomial (n + 1) c β hβ
      (PExponent.single i ⟨1, hq⟩)

end RingHom

section Uniqueness

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [CharP A p]
variable {ι : Type*} {b : ι → k}

/-- 核を一つの Frobenius 冪が消す場合、p-basis の像と剰余写像が持ち上げを決定する。 -/
theorem IsPBasis.ringHom_lift_unique_of_frobenius_kernel (hb : IsPBasis k p b)
    (f : A →+* B) (n : ℕ) (hkill : ∀ x, f x = 0 → x ^ p ^ n = 0)
    (l₁ l₂ : k →+* A) (hres : f.comp l₁ = f.comp l₂)
    (hbmap : ∀ i, l₁ (b i) = l₂ (b i)) : l₁ = l₂ := by
  apply hb.ringHom_ext_of_eq_pow_exp l₁ l₂ hbmap n
  intro x
  have hx : f (l₁ x - l₂ x) = 0 := by
    rw [map_sub, show f (l₁ x) = f (l₂ x) from RingHom.congr_fun hres x, sub_self]
  have hz := hkill (l₁ x - l₂ x) hx
  rw [sub_pow_expChar_pow] at hz
  simpa only [map_pow] using sub_eq_zero.mp hz

/-- 冪零核の場合の指定 p-basis 持ち上げの一意性。全射性・局所性は不要。 -/
theorem IsPBasis.ringHom_lift_unique_of_nilpotent_kernel (hb : IsPBasis k p b)
    (f : A →+* B) (hker : IsNilpotent (RingHom.ker f))
    (l₁ l₂ : k →+* A) (hres : f.comp l₁ = f.comp l₂)
    (hbmap : ∀ i, l₁ (b i) = l₂ (b i)) : l₁ = l₂ := by
  obtain ⟨n, hn⟩ := exists_pow_exp_eq_zero_of_nilpotent_ideal p (RingHom.ker f) hker
  exact hb.ringHom_lift_unique_of_frobenius_kernel f n (fun x hx ↦ hn x hx) l₁ l₂ hres hbmap

/-- 核について分離なら、剰余写像と指定p-basisの像が持ち上げを一意に決める。
存在に必要な完備性・全射性・局所性を一意性には要求しない。 -/
theorem IsPBasis.ringHom_lift_unique_of_hausdorff_kernel (hb : IsPBasis k p b)
    (f : A →+* B) [IsHausdorff (RingHom.ker f) A]
    (l₁ l₂ : k →+* A) (hres : f.comp l₁ = f.comp l₂)
    (hbmap : ∀ i, l₁ (b i) = l₂ (b i)) : l₁ = l₂ := by
  let I := RingHom.ker f
  ext x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have he := hb.ringHom_ext_of_eq_pow_exp
      ((Ideal.Quotient.mk (I ^ (n + 1))).comp l₁)
      ((Ideal.Quotient.mk (I ^ (n + 1))).comp l₂)
      (fun i ↦ congrArg (Ideal.Quotient.mk (I ^ (n + 1))) (hbmap i))
      (n + 1) (fun y ↦ ?_)
    · have hx := RingHom.congr_fun he x
      simpa only [smul_eq_mul, Ideal.mul_top] using
        (SModEq.sub_mem.mpr (Ideal.Quotient.eq.mp hx) :
          l₁ x ≡ l₂ x [SMOD I ^ (n + 1)])
    · apply Ideal.Quotient.eq.mpr
      change l₁ (y ^ p ^ (n + 1)) - l₂ (y ^ p ^ (n + 1)) ∈ I ^ (n + 1)
      rw [map_pow, map_pow, ← sub_pow_expChar_pow]
      have hy : l₁ y - l₂ y ∈ I := by
        change f (l₁ y - l₂ y) = 0
        rw [map_sub, show f (l₁ y) = f (l₂ y) from RingHom.congr_fun hres y, sub_self]
      exact Ideal.pow_le_pow_right (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
        (Ideal.pow_mem_pow hy _)

end Uniqueness

section Lift

variable {k A ι : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime]
  [CharP k p] [CharP A p] {b : ι → k}

/-- 核の元を `p^n` 乗が消す全射 `f : A → k` に沿う切断で、`b_i` を指定した持ち上げ `β_i` へ送るもの。 -/
def IsPBasis.liftOfFrobeniusKernel (hb : IsPBasis k p b) (f : A →+* k)
    (hf : Function.Surjective f) (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0)
    (β : ι → A) (hβ : ∀ i, f (β i) = b i) : k →+* A :=
  hb.ringHomOfFrobeniusRelations n (frobeniusCoefficientLift p f hf n hkill) β fun i ↦ by
    rw [← hβ i]
    exact (frobeniusCoefficientLift_pow p f hf n hkill (β i)).symm

variable (hb : IsPBasis k p b) (f : A →+* k) (hf : Function.Surjective f) (n : ℕ)
  (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) (β : ι → A) (hβ : ∀ i, f (β i) = b i)

@[simp] theorem IsPBasis.liftOfFrobeniusKernel_apply (i : ι) :
    hb.liftOfFrobeniusKernel f hf n hkill β hβ (b i) = β i :=
  hb.ringHomOfFrobeniusRelations_apply _ _ _ _ i

/-- 持ち上げは `f` の切断。 -/
@[simp] theorem IsPBasis.comp_liftOfFrobeniusKernel :
    f.comp (hb.liftOfFrobeniusKernel f hf n hkill β hβ) = RingHom.id k := by
  refine hb.ringHom_ext_of_eq_pow_exp _ (RingHom.id k) (fun i ↦ ?_) n (fun x ↦ ?_)
  · change f (hb.liftOfFrobeniusKernel f hf n hkill β hβ (b i)) = b i
    rw [hb.liftOfFrobeniusKernel_apply, hβ]
  · change f (hb.liftOfFrobeniusKernel f hf n hkill β hβ (x ^ p ^ n)) = x ^ p ^ n
    have h := hb.ringHomOfFrobeniusRelations_coe n (frobeniusCoefficientLift p f hf n hkill) β
      (fun i ↦ by rw [← hβ i]; exact (frobeniusCoefficientLift_pow p f hf n hkill (β i)).symm)
      (frobeniusPowerEquiv k p n x)
    change hb.liftOfFrobeniusKernel f hf n hkill β hβ (x ^ p ^ n) = _ at h
    rw [h]
    exact map_frobeniusCoefficientLift p f hf n hkill (frobeniusPowerEquiv k p n x)

end Lift

/-- 冪零核の場合：指定 p 基底の像を持つ切断は存在して一意。 -/
theorem IsPBasis.existsUnique_ringHom_lift_of_nilpotent_kernel {k A ι : Type*} [Field k]
    [CommRing A] {p : ℕ} [Fact p.Prime] [CharP k p] [CharP A p] {b : ι → k}
    (hb : IsPBasis k p b)
    (f : A →+* k) (hf : Function.Surjective f) (hker : IsNilpotent (RingHom.ker f))
    (β : ι → A) (hβ : ∀ i, f (β i) = b i) :
    ∃! g : k →+* A, f.comp g = RingHom.id k ∧ ∀ i, g (b i) = β i := by
  obtain ⟨n, hn⟩ := exists_pow_exp_eq_zero_of_nilpotent_ideal p (RingHom.ker f) hker
  let hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0 := fun x hx ↦ hn x hx
  refine ⟨hb.liftOfFrobeniusKernel f hf n hkill β hβ,
    ⟨hb.comp_liftOfFrobeniusKernel f hf n hkill β hβ,
      hb.liftOfFrobeniusKernel_apply f hf n hkill β hβ⟩, ?_⟩
  intro l hl
  exact hb.ringHom_lift_unique_of_frobenius_kernel f n hkill l _
    (hl.1.trans (hb.comp_liftOfFrobeniusKernel f hf n hkill β hβ).symm)
    (fun i ↦ (hl.2 i).trans (hb.liftOfFrobeniusKernel_apply f hf n hkill β hβ i).symm)

end SerrePositivity
