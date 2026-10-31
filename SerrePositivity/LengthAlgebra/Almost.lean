module

public import SerrePositivity.CommutativeAlgebra.Almost.Category
public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.CommutativeAlgebra.Almost.Quotient
public import SerrePositivity.LengthAlgebra.Normalized
public import SerrePositivity.CommutativeAlgebra.Almost.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # almost 同型と長さ

## 概要

冪ねじれの almost zero 加群が長さ零なら、almost 局所化圏で同型な対象の長さが一致する。全射な係数変更の像イデアルの冪等性だけを要求して商環の almost 同型から元の長さの一致を導き、零化イデアルで割った作用でも比較する。正規化長さが有限生成部分加群の上限なら、`J^n` と `I` で消える加群の長さ零は巡回加群 `R/(J^n + I)` の長さ零から従い、さらに `R/(J + I)` の長さ零に帰着する。

## 方針

加群を巡回部分加群の和として表し、冪で消える有限生成加群を J M と M/J M に分けて帰納する。

## 規約

almost zero から長さ零への CLMST の結果は明示的な前提として受け取り、文献の結果と同一視しない。Noether 性も almost なイデアルの冪等性も要らない。

## 使われ方

CLMST の almost な長さの比較と正規化長さの消滅。
-/

@[expose] public noncomputable section

universe u

section AlmostQuotientPart

namespace SerrePositivity.LengthAlgebra
open CategoryTheory

variable {R : Type u} [CommRing R] (I J : Ideal R) [Fact (I * I = I)]
    (lam : NormalizedLength R J)

/-- 冪ねじれの almost zero 対象の長さが零なら、almost 圏で同型な対象の長さは一致する。
局所化圏の射を分数で表す一般論と、長さの短完全列での加法性を使う。 -/
theorem length_eq_of_almost_iso
    (hzero : ∀ M : PowTorsionModule J, Almost.IsAlmostZero I M.obj → lam.len M.obj = 0)
    {M N : PowTorsionModule J}
    (e : (Almost.torsionLocalization I J).obj M ≅ (Almost.torsionLocalization I J).obj N) :
    lam.len M.obj = lam.len N.obj :=
  additiveLength_eq_of_localization_iso (Almost.torsionZeroObjects I J) (torsionLength lam)
    (torsionLength_iso lam) (torsionLength_add lam) hzero e

end SerrePositivity.LengthAlgebra

end AlmostQuotientPart

section AlmostBaseChangePart

namespace SerrePositivity.LengthAlgebra
open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I J : Ideal R) [Fact ((I.map (algebraMap R S)) * (I.map (algebraMap R S)) =
      I.map (algebraMap R S))]
    (lam : NormalizedLength R J)

/-- 商環で almost 同型な冪ねじれ加群の、元の環への係数制限で測った長さは一致する。
元の環で almost zero が長さ零となる条件を、全射係数変更と短完全列の加法性で移す。 -/
theorem length_eq_of_almost_iso_baseChange
    (hs : Function.Surjective (algebraMap R S))
    (hzero : ∀ X : PowTorsionModule J, Almost.IsAlmostZero I X.obj → lam.len X.obj = 0)
    {M N : PowTorsionModule (J.map (algebraMap R S))}
    (e : (Almost.torsionLocalization (I.map (algebraMap R S))
      (J.map (algebraMap R S))).obj M ≅
      (Almost.torsionLocalization (I.map (algebraMap R S))
        (J.map (algebraMap R S))).obj N) :
    (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl).len M.obj =
      (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl).len N.obj := by
  apply length_eq_of_almost_iso (I.map (algebraMap R S)) (J.map (algebraMap R S))
    (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl) _ e
  intro X hX
  let := Module.compHom X.obj (algebraMap R S)
  let : IsScalarTower R S X.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hIRX : Almost.IsAlmostZero I X.obj :=
    (Almost.isAlmostZero_map_iff_of_surjective I hs).mp hX
  let XR : PowTorsionModule J :=
    ⟨(ModuleCat.restrictScalars (algebraMap R S)).obj X.obj,
      IsPowTorsion.comap (algebraMap R S) le_rfl X.obj X.property⟩
  exact hzero XR hIRX

/-- 商環の全加群の almost 圏で同型な対象についても、元の長さは一致する。
原典の M^a≃N^a を、冪ねじれ部分圏内の同型だけに制限しない。 -/
theorem length_eq_of_full_almost_iso_baseChange
    (hs : Function.Surjective (algebraMap R S))
    (hzero : ∀ X : PowTorsionModule J, Almost.IsAlmostZero I X.obj → lam.len X.obj = 0)
    {M N : PowTorsionModule (J.map (algebraMap R S))}
    (e : (Almost.localization (I.map (algebraMap R S))).obj M.obj ≅
      (Almost.localization (I.map (algebraMap R S))).obj N.obj) :
    (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl).len M.obj =
      (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl).len N.obj := by
  obtain ⟨e'⟩ := Almost.isTorsionIsomorphic_of_iso
    (I.map (algebraMap R S)) (J.map (algebraMap R S)) M N e
  exact length_eq_of_almost_iso_baseChange I J lam hs hzero e'

end SerrePositivity.LengthAlgebra

end AlmostBaseChangePart

section AlmostQuotientActionPart

namespace SerrePositivity.LengthAlgebra
open CategoryTheory

variable {R : Type u} [CommRing R]

/-- K が加群を零化するとき、構成した商環作用に沿う長さは元の長さと一致する。 -/
@[simp] theorem quotient_comap_len (K J : Ideal R) (lam : NormalizedLength R J)
    (M : Type u) [AddCommGroup M] [Module R M] (hK : Almost.IsAlmostZero K M) :
    let _ := Almost.quotientModule K M hK
    (lam.comap (Ideal.Quotient.mk K) (J.map (Ideal.Quotient.mk K)) le_rfl).len M =
      lam.len M := by
  let := Almost.quotientModule K M hK
  rfl

/-- 構成した商環作用では、像イデアルの冪ねじれ条件と元の条件は一致する。 -/
theorem isPowTorsion_quotientModule_iff (K J : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] (hK : Almost.IsAlmostZero K M) :
    let _ := Almost.quotientModule K M hK
    IsPowTorsion (J.map (Ideal.Quotient.mk K)) M ↔ IsPowTorsion J M := by
  let := Almost.quotientModule K M hK
  let := Almost.quotientModule_scalarTower K M hK
  exact Almost.isPowTorsion_map_iff_of_surjective J Ideal.Quotient.mk_surjective

/-- K で零化される元の加群が、商環の全加群の almost 圏で同型なら、元の長さは一致する。
元のイデアル I の冪等性や単一の almost 同型写像の存在を仮定しない。 -/
theorem length_eq_of_quotient_almost_iso (K I J : Ideal R)
    [Fact ((I.map (Ideal.Quotient.mk K)) * (I.map (Ideal.Quotient.mk K)) =
      I.map (Ideal.Quotient.mk K))]
    (lam : NormalizedLength R J)
    (hzero : ∀ X : PowTorsionModule J, Almost.IsAlmostZero I X.obj → lam.len X.obj = 0)
    (M N : ModuleCat.{u} R) (hM : IsPowTorsion J M) (hN : IsPowTorsion J N)
    (hKM : Almost.IsAlmostZero K M) (hKN : Almost.IsAlmostZero K N) :
    let _ := Almost.quotientModule K M hKM
    let _ := Almost.quotientModule K N hKN
    ((Almost.localization (I.map (Ideal.Quotient.mk K))).obj
      (ModuleCat.of (R ⧸ K) M) ≅
      (Almost.localization (I.map (Ideal.Quotient.mk K))).obj
        (ModuleCat.of (R ⧸ K) N)) → lam.len M = lam.len N := by
  let := Almost.quotientModule K M hKM
  let := Almost.quotientModule K N hKN
  dsimp only
  intro e
  let MQ : PowTorsionModule (J.map (Ideal.Quotient.mk K)) :=
    ⟨ModuleCat.of (R ⧸ K) M, (isPowTorsion_quotientModule_iff K J M hKM).mpr hM⟩
  let NQ : PowTorsionModule (J.map (Ideal.Quotient.mk K)) :=
    ⟨ModuleCat.of (R ⧸ K) N, (isPowTorsion_quotientModule_iff K J N hKN).mpr hN⟩
  have heq := length_eq_of_full_almost_iso_baseChange I J lam
    (S := R ⧸ K) Ideal.Quotient.mk_surjective hzero (M := MQ) (N := NQ) e
  exact (quotient_comap_len K J lam M hKM).symm.trans
    (heq.trans (quotient_comap_len K J lam N hKN))

end SerrePositivity.LengthAlgebra

end AlmostQuotientActionPart

section AlmostVanishingPart

namespace SerrePositivity.LengthAlgebra

variable {R : Type u} [CommRing R] (I J : Ideal R) (lam : NormalizedLength R J)

/-- 固定した冪で消える almost zero 加群の長さ零を、一つの巡回商の長さ零に還元する。 -/
theorem length_eq_zero_of_cyclic_quotient (hsup : lam.HasSup) (n : ℕ)
    (hcyclic : lam.len (R ⧸ (J ^ n ⊔ I)) = 0)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : Module.IsTorsionBySet R M (J ^ n : Ideal R))
    (halmost : Almost.IsAlmostZero I M) : lam.len M = 0 := by
  let K : Ideal R := J ^ n ⊔ I
  have hK : K ≤ Module.annihilator R M := by
    apply sup_le
    · rw [Module.isTorsionBySet_iff_subset_annihilator] at hM
      exact hM
    · exact halmost
  have hquot : IsPowTorsion J (R ⧸ K) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    exact le_sup_left
  let g : M → (R ⧸ K) →ₗ[R] M := fun x ↦
    K.liftQ (LinearMap.toSpanSingleton R M x) (fun a ha ↦ by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Module.mem_annihilator.mp (hK ha) x)
  have hzero : ∀ x, lam.len (LinearMap.range (g x)) = 0 := by
    intro x
    exact le_antisymm ((lam.len_range_le (g x) hquot).trans (le_of_eq hcyclic)) zero_le
  have htop : (⨆ x, LinearMap.range (g x)) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    apply Submodule.mem_iSup_of_mem x
    refine ⟨Submodule.Quotient.mk 1, ?_⟩
    simp only [g, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  have he := NormalizedLength.len_iSup_eq_zero hsup ⟨n, hM⟩
    (fun x ↦ LinearMap.range (g x)) hzero
  rw [htop] at he
  exact (lam.len_congr _ _ Submodule.topEquiv.symm).trans he

/-- 各冪に対応する巡回商が長さ零なら、冪ねじれ almost zero 加群はすべて長さ零。 -/
theorem length_eq_zero_of_cyclic_quotients (hsup : lam.HasSup)
    (hcyclic : ∀ n : ℕ, lam.len (R ⧸ (J ^ n ⊔ I)) = 0)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsPowTorsion J M) (halmost : Almost.IsAlmostZero I M) : lam.len M = 0 := by
  obtain ⟨n, hn⟩ := hM
  exact length_eq_zero_of_cyclic_quotient I J lam hsup n (hcyclic n) M hn halmost

/-- almost zero の長さ消滅は、冪ごとの巡回商での確認と同値。
外部から必要な消滅定理をこの具体的な商の評価に限定できる。 -/
theorem length_eq_zero_for_almost_zero_iff (hsup : lam.HasSup) :
    (∀ (M : Type u) [AddCommGroup M] [Module R M],
      IsPowTorsion J M → Almost.IsAlmostZero I M → lam.len M = 0) ↔
      ∀ n : ℕ, lam.len (R ⧸ (J ^ n ⊔ I)) = 0 := by
  constructor
  · intro h n
    apply h
    · refine ⟨n, ?_⟩
      rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
        Ideal.annihilator_quotient]
      exact le_sup_left
    · change I ≤ Module.annihilator R (R ⧸ (J ^ n ⊔ I))
      rw [Ideal.annihilator_quotient]
      exact le_sup_right
  · intro h M _ _ hM halmost
    exact length_eq_zero_of_cyclic_quotients I J lam hsup h M hM halmost

end SerrePositivity.LengthAlgebra

end AlmostVanishingPart

section CyclicPowerReductionPart

namespace SerrePositivity.LengthAlgebra
open scoped ENNReal
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 有限生成加群が長さ零の巡回商 R/K の全射像の有限和なら、その長さは零。
加法性を適用するため、巡回商と加群の冪ねじれ性を明示する。 -/
theorem length_eq_zero_of_finite_of_cyclic_quotient (K : Ideal R)
    (hK : IsPowTorsion J (R ⧸ K)) (hzero : lam.len (R ⧸ K) = 0)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : IsPowTorsion J M) (hann : K ≤ Module.annihilator R M) : lam.len M = 0 := by
  let f (x : M) : R ⧸ K →ₗ[R] M :=
    K.liftQ (LinearMap.toSpanSingleton R M x) (fun a ha ↦ by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Module.mem_annihilator.mp (hann ha) x)
  let V (x : M) := LinearMap.range (f x)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  have htop : s.sup V = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    apply (Finset.le_sup hx : V x ≤ s.sup V)
    refine ⟨Submodule.Quotient.mk 1, ?_⟩
    change (1 : R) • x = x
    exact one_smul R x
  have hle := lam.len_finset_sup_le hM s V
  rw [← Finset.sup_eq_iSup, htop,
    ← lam.len_congr M (⊤ : Submodule R M) Submodule.topEquiv.symm] at hle
  apply le_antisymm _ zero_le
  refine hle.trans (le_of_eq (Finset.sum_eq_zero fun x _ ↦ ?_))
  exact lam.len_range_eq_zero (f x) hK hzero

/-- 一次の巡回商の長さ零から、有限生成の冪ねじれ almost zero 加群の長さ零を導く。
J M の有限生成性だけに J.FG を用いる。 -/
theorem length_eq_zero_of_finite_of_first_cyclic_quotient (I : Ideal R) (hJ : J.FG)
    (hzero : lam.len (R ⧸ (J ⊔ I)) = 0) (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.IsTorsionBySet R M (J ^ n : Ideal R))
    (hI : Almost.IsAlmostZero I M) : lam.len M = 0 := by
  induction n generalizing M with
  | zero =>
      have hz (x : M) : x = 0 := by
        simpa using hM (x := x) (a := ⟨1, by simp⟩)
      let : Subsingleton M := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
      exact lam.len_eq_zero_of_subsingleton M
  | succ n ih =>
      let N : Submodule R M := J • ⊤
      let : Module.Finite R N := Module.Finite.of_fg (Submodule.FG.smul hJ Module.Finite.fg_top)
      have hN : Module.IsTorsionBySet R N (J ^ n : Ideal R) := by
        intro x a
        apply Subtype.ext
        change (a : R) • (x : M) = 0
        refine Submodule.smul_induction_on (p := fun z : M ↦ (a : R) • z = 0) x.2 ?_ ?_
        · intro b hb m _
          rw [← mul_smul]
          exact hM (x := m) (a := ⟨(a : R) * b, by
            rw [pow_succ]
            exact Ideal.mul_mem_mul a.2 hb⟩)
        · intro x y hx hy
          rw [smul_add, hx, hy, add_zero]
      have hQ : Module.IsTorsionBySet R (M ⧸ N) (J ^ 1 : Ideal R) := by
        intro q a
        induction q using Submodule.Quotient.induction_on with
        | _ x =>
          apply (Submodule.Quotient.mk_eq_zero N).mpr
          exact Submodule.smul_mem_smul (by simpa using a.2) (Submodule.mem_top : x ∈ ⊤)
      have hquot : IsPowTorsion J (R ⧸ (J ⊔ I)) := by
        refine ⟨1, ?_⟩
        rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
          Ideal.annihilator_quotient, pow_one]
        exact le_sup_left
      have hQann : J ⊔ I ≤ Module.annihilator R (M ⧸ N) := by
        apply sup_le
        · rw [← pow_one J]
          have hh := hQ
          rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe] at hh
          exact hh
        · exact hI.quotient N
      have hNzero := ih N hN (hI.submodule N)
      have hQzero := length_eq_zero_of_finite_of_cyclic_quotient lam (J ⊔ I) hquot hzero
        (M ⧸ N) ⟨1, hQ⟩ hQann
      rw [lam.len_eq_add_quotient ⟨n + 1, hM⟩ N, hNzero, hQzero, add_zero]

/-- 一次の巡回商の長さ零から、全ての冪の巡回商の長さ零を証明する。 -/
theorem cyclic_quotient_pow_length_eq_zero_of_first (I : Ideal R) (hJ : J.FG)
    (hzero : lam.len (R ⧸ (J ⊔ I)) = 0) (n : ℕ) :
    lam.len (R ⧸ (J ^ n ⊔ I)) = 0 := by
  apply length_eq_zero_of_finite_of_first_cyclic_quotient lam I hJ hzero n
  · rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    exact le_sup_left
  · change I ≤ Module.annihilator R (R ⧸ (J ^ n ⊔ I))
    rw [Ideal.annihilator_quotient]
    exact le_sup_right

end SerrePositivity.LengthAlgebra

end CyclicPowerReductionPart
