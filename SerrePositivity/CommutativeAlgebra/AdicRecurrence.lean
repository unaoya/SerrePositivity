module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # 主イデアル進完備加群の列と漸化式

f進完備加群では、列の作用xₙ ↦ xₙ-fxₙ₊₁が全単射となる。
導来完備性比較のtelescope計算に使う加群上の部品であり、
このファイルだけで導来圏の全次数の消滅を結論しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
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

/-- 分離加群への局所化からの線形写像は零。導来比較の零次数部分。 -/
theorem linearMap_away_eq_zero_of_isHausdorff (f : R)
    [IsHausdorff (Ideal.span {f}) M] (g : Localization.Away f →ₗ[R] M) : g = 0 := by
  ext z
  apply IsHausdorff.haus' (I := Ideal.span {f})
  intro n
  apply SModEq.sub_mem.mpr
  simp only [sub_zero]
  apply (mem_principal_pow_smul_top f n _).mpr
  obtain ⟨w, hw⟩ := (IsUnit.isUnit_iff_mulLeft_bijective.mp
    (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away f) f n)).2 z
  change (algebraMap R (Localization.Away f) f) ^ n * w = z at hw
  refine ⟨g w, ?_⟩
  rw [← g.map_smul]
  rw [Algebra.smul_def, map_pow, hw]

end SerrePositivity
