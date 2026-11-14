module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Algebra.Algebra.Subalgebra.Pi
public import Mathlib.RingTheory.Finiteness.Cardinality
public import SerrePositivity.BhattScholze.Andre.Transfinite.Limit
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid

/-!
# 自明なエタール被覆の比較環

## 概要
BS 著者版 Theorem 10.9 の証明で使う、主局所化で直積に分裂する代数の比較環を扱う。

## 方針
分裂した各成分で元の代数の像を取る。直積の座標冪等元で成分を分離する。

## 規約
比較環は分裂した局所化の中の部分代数とする。

## 使われ方
Corollary 8.12 の適用に必要な比較写像を供給する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Almost

open SerrePositivity.DerivedCompletion

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Theorem 10.9 の自明な有限エタール被覆を指定する局所化の分裂。 -/
abbrev AwaySplitting (g : R) (r : ℕ) :=
  letI := GenericEtale.awayAlgebra R S g
  Localization.Away (algebraMap R S g) ≃ₐ[Localization.Away g] (Fin r → Localization.Away g)

/-- 分裂した主局所化への元の代数の射。 -/
def splitSource (g : R) (r : ℕ) (e : AwaySplitting R S g r) :
    S →ₐ[R] (Fin r → Localization.Away g) := by
  letI := GenericEtale.awayAlgebra R S g
  let B := Localization.Away (algebraMap R S g)
  letI : IsScalarTower R (Localization.Away g) B := GenericEtale.awayAlgebra_scalarTower R S g
  exact (e.restrictScalars R).toAlgHom.comp (IsScalarTower.toAlgHom R S B)

/-- 基底環の直積から分裂した主局所化への座標ごとの射。 -/
def splitProduct (g : R) (r : ℕ) : (Fin r → R) →ₐ[R] (Fin r → Localization.Away g) where
  toFun x i := algebraMap R _ (x i)
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intros; ext; simp
  map_mul' := by intros; ext; simp
  commutes' := by intros; rfl

/-- Theorem 10.9 の比較環。分裂した局所化の中で二つの像が生成する部分代数。 -/
def trivialCoverComparison (g : R) (r : ℕ) (e : AwaySplitting R S g r) :
    Subalgebra R (Fin r → Localization.Away g) :=
  (splitSource R S g r e).range ⊔ (splitProduct R g r).range

/-- 元の代数から比較環への射。 -/
def sourceToComparison (g : R) (r : ℕ) (e : AwaySplitting R S g r) :
    S →ₐ[R] trivialCoverComparison R S g r e :=
  (splitSource R S g r e).codRestrict _
    (fun x => IsConcreteLE.le_iff.mp le_sup_left (Set.mem_range_self x))

/-- 基底環の直積から比較環への射。 -/
def productToComparison (g : R) (r : ℕ) (e : AwaySplitting R S g r) :
    (Fin r → R) →ₐ[R] trivialCoverComparison R S g r e :=
  (splitProduct R g r).codRestrict _
    (fun x => IsConcreteLE.le_iff.mp le_sup_right (Set.mem_range_self x))

private def splitCoordinate (g : R) (r : ℕ) (e : AwaySplitting R S g r) (i : Fin r) :
    S →ₐ[R] Localization.Away g :=
  (Pi.evalAlgHom R (fun _ : Fin r => Localization.Away g) i).comp (splitSource R S g r e)

private theorem trivialCoverComparison_eq_pi (g : R) (r : ℕ) (e : AwaySplitting R S g r) :
    trivialCoverComparison R S g r e = Subalgebra.pi Set.univ
      (fun i => (splitCoordinate R S g r e i).range) := by
  classical
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨s, rfl⟩
      exact fun _ _ => ⟨s, rfl⟩
    · rintro _ ⟨x, rfl⟩
      intro i _
      refine ⟨algebraMap R S (x i), ?_⟩
      exact (splitCoordinate R S g r e i).commutes (x i)
  · intro x hx
    choose s hs using fun i => hx i (Set.mem_univ i)
    have hterm (i : Fin r) : splitProduct R g r (Pi.single i 1) *
        splitSource R S g r e (s i) ∈ trivialCoverComparison R S g r e :=
      (trivialCoverComparison R S g r e).mul_mem
        (IsConcreteLE.le_iff.mp le_sup_right (Set.mem_range_self _))
        (IsConcreteLE.le_iff.mp le_sup_left (Set.mem_range_self _))
    have he : (∑ i, splitProduct R g r (Pi.single i 1) *
        splitSource R S g r e (s i)) = x := by
      ext j
      simp only [Finset.sum_apply, Pi.mul_apply, splitProduct, AlgHom.coe_mk, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk]
      rw [Finset.sum_eq_single j]
      · simpa [splitCoordinate] using hs j
      · intro i _ hij
        simp [Pi.single_eq_of_ne (Ne.symm hij)]
      · simp
    rw [← he]
    exact Subalgebra.sum_mem _ fun i _ => hterm i

/-- Theorem 10.9 の比較環は元の代数が有限なら有限。 -/
theorem trivialCoverComparison_finite [Module.Finite R S] (g : R) (r : ℕ)
    (e : AwaySplitting R S g r) : Module.Finite R (trivialCoverComparison R S g r e) := by
  rw [trivialCoverComparison_eq_pi]
  let f : (Fin r → S) →ₗ[R] (Fin r → Localization.Away g) :=
    LinearMap.pi fun i => (splitCoordinate R S g r e i).toLinearMap.comp (LinearMap.proj i)
  have hmem (x : Fin r → S) : f x ∈ Subalgebra.pi Set.univ
      (fun i => (splitCoordinate R S g r e i).range) := fun i _ => ⟨x i, rfl⟩
  apply Module.Finite.of_surjective (f.codRestrict _ hmem)
  intro x
  choose y hy using fun i => x.property i (Set.mem_univ i)
  exact ⟨y, Subtype.ext (funext hy)⟩

private theorem integral_of_finite_target {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R B] (f : A →ₐ[R] B) : f.toRingHom.IsIntegral := by
  apply RingHom.IsIntegral.tower_top (algebraMap R A) f.toRingHom
  exact f.comp_algebraMap.symm ▸ (show (algebraMap R B).IsIntegral from
    fun x => IsIntegral.of_finite R x)

/-- Theorem 10.9 の比較環への二射は整。 -/
theorem trivialCoverComparison_integral [Module.Finite R S] (g : R) (r : ℕ)
    (e : AwaySplitting R S g r) :
    (sourceToComparison R S g r e).toRingHom.IsIntegral ∧
      (productToComparison R S g r e).toRingHom.IsIntegral := by
  let := trivialCoverComparison_finite R S g r e
  exact ⟨integral_of_finite_target R (sourceToComparison R S g r e),
    integral_of_finite_target R (productToComparison R S g r e)⟩

private theorem clearSplitDenominators {ι : Type*} [Finite ι] (g : R)
    (x : ι → Localization.Away g) :
    ∃ n : ℕ, ∃ y : ι → R, ∀ i, algebraMap R (Localization.Away g) (y i) =
      (algebraMap R (Localization.Away g) g) ^ n * x i := by
  classical
  let := Fintype.ofFinite ι
  let a := algebraMap R (Localization.Away g)
  let s := fun i => IsLocalization.Away.sec g (x i)
  let n := Finset.univ.sup fun i => (s i).2
  refine ⟨n, fun i => g ^ (n - (s i).2) * (s i).1, ?_⟩
  intro i
  have hi : (s i).2 ≤ n := Finset.le_sup (f := fun i => (s i).2) (Finset.mem_univ i)
  have he : a (s i).1 = a g ^ (s i).2 * x i := by
    rw [← map_pow, mul_comm]
    exact (IsLocalization.Away.sec_spec g (x i)).symm
  rw [map_mul, map_pow, he, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]

/-- Theorem 10.9 の比較環への二射は、指定した主局所化で同型になる。 -/
theorem trivialCoverComparison_localization_iso (g : R) (r : ℕ) (e : AwaySplitting R S g r) :
    Function.Bijective (Localization.awayMap (sourceToComparison R S g r e).toRingHom
      (algebraMap R S g)) ∧
    Function.Bijective (Localization.awayMap (productToComparison R S g r e).toRingHom
      (algebraMap R (Fin r → R) g)) := by
  let := GenericEtale.awayAlgebra R S g
  let a := algebraMap R S g
  let B := Localization.Away a
  constructor <;> constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro x hx
    have hx' : e (algebraMap S B x) = 0 := congrArg Subtype.val hx
    have hz : algebraMap S B x = 0 := e.injective (hx'.trans e.map_zero.symm)
    obtain ⟨⟨y, n, rfl⟩, hy⟩ := (IsLocalization.map_eq_zero_iff (.powers a) B x).mp hz
    exact ⟨n, hy⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro x
    let y := e.symm (x : Fin r → Localization.Away g)
    refine ⟨(IsLocalization.Away.sec a y).1, (IsLocalization.Away.sec a y).2, ?_⟩
    apply Subtype.ext
    change e (algebraMap S B (IsLocalization.Away.sec a y).1) =
      (e (algebraMap S B a)) ^ (IsLocalization.Away.sec a y).2 * (x : Fin r → Localization.Away g)
    simpa only [map_mul, map_pow, mul_comm, y, AlgEquiv.apply_symm_apply] using
      congrArg e (IsLocalization.Away.sec_spec a y).symm
  · classical
    apply Localization.awayMap_injective_iff.mpr
    intro x hx
    have hzero (i : Fin r) : algebraMap R (Localization.Away g) (x i) = 0 :=
      congrFun (congrArg Subtype.val hx) i
    have hpow (i : Fin r) : ∃ n : ℕ, g ^ n * x i = 0 := by
      obtain ⟨⟨y, n, rfl⟩, hy⟩ :=
        (IsLocalization.map_eq_zero_iff (.powers g) (Localization.Away g) (x i)).mp (hzero i)
      exact ⟨n, hy⟩
    choose n hn using hpow
    let N := Finset.univ.sup n
    refine ⟨N, funext fun i => ?_⟩
    change g ^ N * x i = 0
    have hi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hi, pow_add, mul_assoc, hn i, mul_zero]
  · apply Localization.awayMap_surjective_iff.mpr
    intro x
    obtain ⟨n, y, hy⟩ := clearSplitDenominators R g (x : Fin r → Localization.Away g)
    exact ⟨y, n, Subtype.ext (funext hy)⟩


private theorem complete_of_surjective_injective {R L M N : Type u} [CommRing R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : R) (q : L →ₗ[R] M) (hq : Function.Surjective q)
    (z : M →ₗ[R] N) (hz : Function.Injective z)
    (hl : IsModuleComplete R p (ModuleCat.of R L))
    (hn : IsModuleComplete R p (ModuleCat.of R N)) :
    IsModuleComplete R p (ModuleCat.of R M) := by
  have hl' := (isModuleComplete_iff_recurrence_bijective R p (ModuleCat.of R L)).mp hl
  have hn' := (isModuleComplete_iff_recurrence_bijective R p (ModuleCat.of R N)).mp hn
  apply (isModuleComplete_iff_recurrence_bijective R p (ModuleCat.of R M)).mpr
  constructor
  · intro x y hxy
    have he : (fun n => z (x n)) = (fun n => z (y n)) := hn'.injective (by
      funext n
      change z (x n) - p • z (x (n + 1)) = z (y n) - p • z (y (n + 1))
      simp only [← map_smul, ← map_sub]
      exact congrArg z (congrFun hxy n))
    funext n
    exact hz (congrFun he n)
  · intro y
    choose w hw using fun n => hq (y n)
    obtain ⟨v, hv⟩ := hl'.surjective w
    refine ⟨fun n => q (v n), ?_⟩
    funext n
    change q (v n) - p • q (v (n + 1)) = y n
    have hvn : v n - p • v (n + 1) = w n := congrFun hv n
    rw [← map_smul, ← map_sub, hvn, hw]

private theorem splitLocalizationRange_complete (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) :
    IsModuleComplete R (p : R)
      (ModuleCat.of R (Algebra.linearMap R (Localization.Away g)).range) := by
  let L := Localization.Away g
  let l := Algebra.linearMap R L
  let d : R →ₗ[R] R := LinearMap.mulLeft R g
  have hk : l.ker = d.ker := by
    ext x
    change algebraMap R L x = 0 ↔ g * x = 0
    constructor
    · intro hx
      obtain ⟨⟨y, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (.powers g) L x).mp hx
      let : IsReduced R := hR.isReduced
      exact Andre.Transfinite.mul_eq_zero_of_pow_mul_eq_zero_of_reduced g x n hn
    · intro hx
      exact (IsLocalization.map_eq_zero_iff (.powers g) L x).mpr ⟨⟨g, 1, pow_one g⟩, hx⟩
  let e := l.quotKerEquivRange.symm ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ hk) ≪≫ₗ d.quotKerEquivRange
  let z : l.range →ₗ[R] R := d.range.subtype.comp e.toLinearMap
  exact complete_of_surjective_injective (p : R) l.rangeRestrict l.surjective_rangeRestrict
    z (Subtype.val_injective.comp e.injective) (hR.isModuleComplete R p) (hR.isModuleComplete R p)

/-- Theorem 10.9 の比較環は導来 p 完備。有限個の生成元の分母を払って示す。 -/
theorem trivialCoverComparison_isModuleComplete (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) [Module.Finite R S] (g : R) (r : ℕ)
    (e : AwaySplitting R S g r) :
    IsModuleComplete R (p : R) (ModuleCat.of R (trivialCoverComparison R S g r e)) := by
  classical
  let C := trivialCoverComparison R S g r e
  let L := Localization.Away g
  let l := Algebra.linearMap R L
  have hp := hR.isModuleComplete R p
  have hl := splitLocalizationRange_complete R p hR g
  let : Module.Finite R C := trivialCoverComparison_finite R S g r e
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := C)
  obtain ⟨N, y, hy⟩ := clearSplitDenominators R g
    (fun i : Fin n × Fin r => (s i.1 : Fin r → L) i.2)
  let M := Fin r → l.range
  have hm : IsModuleComplete R (p : R) (ModuleCat.of R M) :=
    isModuleComplete_pi R (p : R) (fun _ : Fin r => ModuleCat.of R l.range) (fun _ => hl)
  let f : C →ₗ[R] (Fin r → L) := (g ^ N) • C.val.toLinearMap
  let Q : Submodule R (Fin r → L) := Submodule.pi Set.univ fun _ => l.range
  have hf (x : C) : f x ∈ Q := by
    have hgen : Submodule.span R (Set.range s) ≤ Q.comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩ j _
      refine ⟨y (i, j), ?_⟩
      change algebraMap R L (y (i, j)) = (g ^ N • (s i : Fin r → L) j)
      rw [Algebra.smul_def, map_pow]
      exact hy (i, j)
    exact hgen (hs.symm ▸ Submodule.mem_top)
  let z : C →ₗ[R] M := LinearMap.pi fun j =>
    ((LinearMap.proj j).comp f).codRestrict l.range (fun x => hf x j (Set.mem_univ j))
  have hz : Function.Injective z := by
    intro x x' h
    apply Subtype.ext
    funext j
    have he := congrArg (fun m : M => (m j : L)) h
    have hu := IsLocalization.Away.algebraMap_pow_isUnit (S := L) g N
    apply hu.mul_left_cancel
    change (g ^ N) • (x : Fin r → L) j = (g ^ N) • (x' : Fin r → L) j at he
    simpa only [Algebra.smul_def, map_pow] using he
  obtain ⟨k, q, hq⟩ := Module.Finite.exists_fin' (R := R) (M := C)
  have hfree := isModuleComplete_pi R (p : R) (fun _ : Fin k => ModuleCat.of R R) (fun _ => hp)
  exact complete_of_surjective_injective (p : R) q hq z hz hfree hm

end SerrePositivity.BhattScholze.Almost

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 10.9" (partial := component) "主イデアルへの帰着、分裂比較環、整閉包の完備化（BS-W13）。組み立ては A6・A7 待ち ／ 11-10 更新 ／ 11-12：integralClosureCompletion_isModuleComplete は Thm 10.11 の部品なので列から外した"] _root_.SerrePositivity.BhattScholze.Almost.trivialCoverComparison_localization_iso
