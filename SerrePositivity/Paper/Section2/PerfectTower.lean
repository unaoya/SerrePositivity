module

public import SerrePositivity.Paper.Section2.TowerStage
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# 完全環への塔の標準写像

標数 `p` の完全環では Frobenius の逆により根を一意に選べる。
この根で各段の関係式を満たし、遷移写像との両立から塔全体の代数準同型を構成する。
等標数の定理2.5では、これを `D` の perfection に適用する。
完全環への写像の構成には局所性・正則性や長さの性質は必要ない。
後半では、等標数の有限段から基底への Frobenius 写像も構成する。
基底が完備局所環で剰余体が完全、かつ有限段が被約なら、この写像は環同型になる。
-/

public section
universe u
namespace SerrePositivity.Section2
open MvPolynomial

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime] [CharP C p] [PerfectRing C p]

/-- 完全環内での `tᵢ` の一意な `pⁿ` 乗根。 -/
noncomputable def perfectRoot (n : ℕ) (i : Fin h) : C :=
  (iterateFrobeniusEquiv C p n).symm (algebraMap A C (t i))

/-- 選んだ根は各段の定義関係式を満たす。 -/
theorem perfectRoot_pow (n : ℕ) (i : Fin h) :
    perfectRoot A C t p n i ^ (p ^ n) = algebraMap A C (t i) :=
  (iterateFrobeniusEquiv C p n).apply_symm_apply _

/-- 根の選択は塔の遷移写像と両立する。 -/
theorem perfectRoot_compatible (a b : ℕ) (hab : a ≤ b) (i : Fin h) :
    perfectRoot A C t p b i ^ (p ^ (b - a)) = perfectRoot A C t p a i := by
  apply (iterateFrobeniusEquiv C p a).injective
  change (perfectRoot A C t p b i ^ (p ^ (b - a))) ^ (p ^ a) =
    perfectRoot A C t p a i ^ (p ^ a)
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab, perfectRoot_pow, perfectRoot_pow]

/-- 塔の一つの段から完全環への代数準同型。 -/
noncomputable def towerStageToPerfect (n : ℕ) : TowerStage A t p n →ₐ[A] C :=
  Ideal.Quotient.liftₐ (towerRel A t p n) (aeval (perfectRoot A C t p n))
    (relIdeal_apply_eq_zero t (p ^ n) _ fun i ↦ by
      rw [aeval_X]
      exact perfectRoot_pow A C t p n i)

/-- 段の変数は指定した根に写る。 -/
@[simp] theorem towerStageToPerfect_mk_X (n : ℕ) (i : Fin h) :
    towerStageToPerfect A C t p n (Ideal.Quotient.mk (towerRel A t p n) (X i)) =
      perfectRoot A C t p n i := by
  change aeval (perfectRoot A C t p n) (X i) = _
  rw [aeval_X]

/-- 標数 `p` の有限段では、任意の元の `pⁿ` 乗が基底環から来る。
多項式の和と変数による積に関する帰納法で、定義関係式から直接示す。 -/
theorem towerStage_pow_mem_range (n : ℕ) [CharP (TowerStage A t p n) p]
    (x : TowerStage A t p n) :
    ∃ a : A, algebraMap A (TowerStage A t p n) a = x ^ (p ^ n) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨a ^ (p ^ n), by rw [map_pow]; rfl⟩
  | add f g hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, by rw [map_add, ha, hb, map_add, add_pow_char_pow]⟩
  | mul_X f i hf =>
    obtain ⟨a, ha⟩ := hf
    exact ⟨a * t i, by rw [map_mul, ha, map_mul, mul_pow, mk_X_pow]⟩

/-- 塔の各元は、基底環の元のある `p` 冪根である。
元を一つの有限段に降ろし、その段の Frobenius の公式を使う。 -/
theorem tower_pow_mem_range (hchar : ∀ n, CharP (TowerStage A t p n) p)
    (x : Tower A t p) :
    ∃ n : ℕ, ∃ a : A, algebraMap A (Tower A t p) a = x ^ (p ^ n) := by
  obtain ⟨n, y, rfl⟩ := exists_towerOf A t p x
  let := hchar n
  obtain ⟨a, ha⟩ := towerStage_pow_mem_range A t p n y
  refine ⟨n, a, ?_⟩
  rw [IsScalarTower.algebraMap_apply A (TowerStage A t p n) (Tower A t p), ha, map_pow]
  rfl

/-- 有限段が被約で、基底環の像が単射なら、完全環への標準写像も単射。
核の元の `pⁿ` 乗を基底環に戻し、被約性で元自身が零であることを示す。 -/
theorem towerStageToPerfect_injective (n : ℕ)
    [CharP (TowerStage A t p n) p] [IsReduced (TowerStage A t p n)]
    (hinj : Function.Injective (algebraMap A C)) :
    Function.Injective (towerStageToPerfect A C t p n) := by
  apply (injective_iff_map_eq_zero (towerStageToPerfect A C t p n)).mpr
  intro x hx
  obtain ⟨a, ha⟩ := towerStage_pow_mem_range A t p n x
  have hzero : algebraMap A C a = 0 := by
    rw [← (towerStageToPerfect A C t p n).commutes a, ha, map_pow, hx,
      zero_pow (pow_pos (Fact.out : p.Prime).pos n).ne']
  have ha0 : a = 0 := hinj (hzero.trans (map_zero _).symm)
  exact IsReduced.eq_zero x ⟨p ^ n, by rw [← ha, ha0, map_zero]⟩

/-- 各段からの写像は遷移写像と両立する。 -/
theorem towerStageToPerfect_compatible (a b : ℕ) (hab : a ≤ b)
    (x : TowerStage A t p a) :
    towerStageToPerfect A C t p b (towerMap A t p a b hab x) =
      towerStageToPerfect A C t p a x := by
  have heq : (towerStageToPerfect A C t p b).comp (towerMap A t p a b hab) =
      towerStageToPerfect A C t p a := by
    apply Ideal.Quotient.algHom_ext A
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [towerMap_mk_X, map_pow, towerStageToPerfect_mk_X, towerStageToPerfect_mk_X]
    exact perfectRoot_compatible A C t p a b hab i
  exact AlgHom.congr_fun heq x

/-- 塔全体から完全環への標準環準同型。 -/
noncomputable def towerToPerfectRingHom : Tower A t p →+* C :=
  Ring.DirectLimit.lift _ _ C (fun n ↦ (towerStageToPerfect A C t p n).toRingHom)
    (towerStageToPerfect_compatible A C t p)

/-- 標準写像を各段に制限すると、根による写像に戻る。 -/
@[simp] theorem towerToPerfectRingHom_of (n : ℕ) (x : TowerStage A t p n) :
    towerToPerfectRingHom A C t p (towerOf A t p n x) =
      towerStageToPerfect A C t p n x := by
  exact Ring.DirectLimit.lift_of ..

/-- 塔から完全環への写像は基底 `A` の作用を保つ。 -/
noncomputable def towerToPerfect : Tower A t p →ₐ[A] C where
  __ := towerToPerfectRingHom A C t p
  commutes' x := by
    change towerToPerfectRingHom A C t p (algebraMap A (Tower A t p) x) = _
    rw [algebraMap_tower_apply, towerToPerfectRingHom_of, AlgHom.commutes]

/-- 塔からの代数準同型を一つの段に制限したときの計算規則。 -/
@[simp] theorem towerToPerfect_of (n : ℕ) (x : TowerStage A t p n) :
    towerToPerfect A C t p (towerOf A t p n x) = towerStageToPerfect A C t p n x := by
  exact towerToPerfectRingHom_of A C t p n x

/-- 各有限段が被約なら、基底環を単射に含む完全環への塔全体の写像も単射。
任意の核の元を有限段に降ろし、その段での単射性を適用する。 -/
theorem towerToPerfect_injective
    (hchar : ∀ n, CharP (TowerStage A t p n) p)
    (hred : ∀ n, IsReduced (TowerStage A t p n))
    (hinj : Function.Injective (algebraMap A C)) :
    Function.Injective (towerToPerfect A C t p) := by
  apply (injective_iff_map_eq_zero (towerToPerfect A C t p)).mpr
  intro x hx
  obtain ⟨n, y, rfl⟩ := exists_towerOf A t p x
  rw [towerToPerfect_of] at hx
  let := hchar n
  let := hred n
  have hy : y = 0 := towerStageToPerfect_injective A C t p n hinj
    (hx.trans (map_zero _).symm)
  rw [hy, map_zero]

/-- 各段から完全環への基底を保つ写像は、根の一意性によって一意である。 -/
theorem towerStageToPerfect_unique (n : ℕ) (f : TowerStage A t p n →ₐ[A] C) :
    f = towerStageToPerfect A C t p n := by
  apply Ideal.Quotient.algHom_ext A
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, towerStageToPerfect_mk_X]
  apply (iterateFrobeniusEquiv C p n).injective
  change f (Ideal.Quotient.mk (towerRel A t p n) (X i)) ^ (p ^ n) =
    perfectRoot A C t p n i ^ (p ^ n)
  rw [← map_pow, mk_X_pow, AlgHom.commutes, perfectRoot_pow]

/-- 塔全体から完全環への基底を保つ写像も一意である。 -/
theorem towerToPerfect_unique (f : Tower A t p →ₐ[A] C) :
    f = towerToPerfect A C t p := by
  apply AlgHom.ext
  intro x
  obtain ⟨n, y, rfl⟩ := exists_towerOf A t p x
  let g : TowerStage A t p n →ₐ[A] Tower A t p :=
    { towerOf A t p n with
      commutes' := fun a ↦ (IsScalarTower.algebraMap_apply A (TowerStage A t p n)
        (Tower A t p) a).symm }
  have heq := AlgHom.congr_fun (towerStageToPerfect_unique A C t p n (f.comp g)) y
  exact heq.trans (towerToPerfectRingHom_of A C t p n y).symm

end SerrePositivity.Section2


namespace SerrePositivity.Section2
open MvPolynomial IsLocalRing

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A)
    (p : ℕ) [Fact p.Prime] [CharP A p]

/-- 等標数の有限段から基底環への Frobenius 写像。
係数 `a` は `a^(pⁿ)`、付加したパラメータの根は元のパラメータに送る。 -/
noncomputable def towerStageFrobenius (n : ℕ) : TowerStage A t p n →+* A :=
  Ideal.Quotient.lift _ (eval₂Hom (iterateFrobenius A p n) t) (by
    change towerRel A t p n ≤ RingHom.ker (eval₂Hom (iterateFrobenius A p n) t)
    rw [towerRel, relIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change eval₂Hom (iterateFrobenius A p n) t (X i ^ (p ^ n) - C (t i)) = 0
    rw [map_sub, map_pow, eval₂Hom_X', eval₂Hom_C, iterateFrobenius_def, sub_self])

/-- 有限段の Frobenius 写像は係数上で通常の反復 Frobenius になる。 -/
@[simp] theorem towerStageFrobenius_algebraMap (n : ℕ) (a : A) :
    towerStageFrobenius A t p n (algebraMap A (TowerStage A t p n) a) = a ^ (p ^ n) := by
  change eval₂Hom (iterateFrobenius A p n) t (C a) = _
  rw [eval₂Hom_C, iterateFrobenius_def]

/-- 有限段の Frobenius 写像は、付加した根を元のパラメータに戻す。 -/
@[simp] theorem towerStageFrobenius_stageX (n : ℕ) (i : Fin h) :
    towerStageFrobenius A t p n (stageX A t p n i) = t i := by
  change eval₂Hom (iterateFrobenius A p n) t (X i) = _
  rw [eval₂Hom_X']

/-- 有限段に戻して見ると、上の写像は実際に `pⁿ` 乗を計算する。 -/
theorem towerStageFrobenius_pow (n : ℕ) [CharP (TowerStage A t p n) p]
    (x : TowerStage A t p n) :
    algebraMap A (TowerStage A t p n) (towerStageFrobenius A t p n x) = x ^ (p ^ n) := by
  have heq : (algebraMap A (TowerStage A t p n)).comp (towerStageFrobenius A t p n) =
      iterateFrobenius (TowerStage A t p n) p n := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change algebraMap A (TowerStage A t p n)
        (towerStageFrobenius A t p n (algebraMap A (TowerStage A t p n) a)) = _
      rw [towerStageFrobenius_algebraMap, map_pow]
      rfl
    · intro i
      change algebraMap A (TowerStage A t p n)
        (towerStageFrobenius A t p n (stageX A t p n i)) = _
      rw [towerStageFrobenius_stageX, ← mk_X_pow A t p n i]
      rfl
  exact RingHom.congr_fun heq x

/-- 被約な有限段では、Frobenius 写像は単射。 -/
theorem towerStageFrobenius_injective (n : ℕ) [CharP (TowerStage A t p n) p]
    [IsReduced (TowerStage A t p n)] :
    Function.Injective (towerStageFrobenius A t p n) := by
  intro x y hxy
  apply iterateFrobenius_inj (TowerStage A t p n) p n
  simpa only [towerStageFrobenius_pow, iterateFrobenius_def] using
    congrArg (algebraMap A (TowerStage A t p n)) hxy

/-- 完備局所環の剰余体が完全なら、有限段からの Frobenius 写像は全射。
極大イデアルの生成元は像に入り、剰余体上では完全性から全射になるので、
Mathlib の完備性による全射性判定を適用できる。 -/
theorem towerStageFrobenius_surjective [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [CharP (ResidueField A) p]
    [PerfectRing (ResidueField A) p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (n : ℕ) :
    Function.Surjective (towerStageFrobenius A t p n) := by
  have htmem : ∀ i, t i ∈ maximalIdeal A := fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)
  let := isLocalRing_towerStage A t p htmem n
  let := isAdicComplete_towerStage A t p htmem n
  have hmap : (maximalIdeal (TowerStage A t p n)).map (towerStageFrobenius A t p n) =
      maximalIdeal A := by
    rw [← span_stageX_eq_maximalIdeal A t p htmem ht n, Ideal.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, towerStageFrobenius_stageX] using ht
  let : IsHausdorff ((maximalIdeal (TowerStage A t p n)).map
      (towerStageFrobenius A t p n)) A := hmap.symm ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (towerStageFrobenius A t p n)
    (I := maximalIdeal (TowerStage A t p n))
  have hres : Function.Surjective ((residue A).comp (towerStageFrobenius A t p n)) := by
    intro z
    obtain ⟨w, hw⟩ := (iterateFrobeniusEquiv (ResidueField A) p n).surjective z
    obtain ⟨a, ha⟩ := residue_surjective w
    refine ⟨algebraMap A (TowerStage A t p n) a, ?_⟩
    simpa only [RingHom.comp_apply, towerStageFrobenius_algebraMap, map_pow, ha,
      iterateFrobeniusEquiv_def] using hw
  rw [hmap]
  exact hres

/-- 被約な有限段は、完備性と剰余体の完全性の下で Frobenius により基底環と同型になる。
この同型は `A` 代数同型ではなく、係数に Frobenius を作用させる環同型である。 -/
noncomputable def towerStageFrobeniusEquiv [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [CharP (ResidueField A) p]
    [PerfectRing (ResidueField A) p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (n : ℕ)
    [CharP (TowerStage A t p n) p] [IsReduced (TowerStage A t p n)] :
    TowerStage A t p n ≃+* A :=
  RingEquiv.ofBijective (towerStageFrobenius A t p n)
    ⟨towerStageFrobenius_injective A t p n, towerStageFrobenius_surjective A t p ht n⟩

/-- Frobenius 同型の順写像は、構成した有限段の Frobenius 写像である。 -/
@[simp] theorem towerStageFrobeniusEquiv_apply [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [CharP (ResidueField A) p]
    [PerfectRing (ResidueField A) p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (n : ℕ)
    [CharP (TowerStage A t p n) p] [IsReduced (TowerStage A t p n)]
    (x : TowerStage A t p n) :
    towerStageFrobeniusEquiv A t p ht n x = towerStageFrobenius A t p n x := by
  rfl

end SerrePositivity.Section2
