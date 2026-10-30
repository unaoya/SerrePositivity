module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Pi
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.LocalRing.Pullback

/-! # スカラーによる同種写像

## 概要

核と余核がスカラー a の冪で消える写像（スカラー同種写像）の性質：逆向きの同種写像の存在、テンソル積との両立、有限自由加群を経由する分解、有限積の同種写像、被約な有限自由の場合、有限表示の持ち上げ、引き戻しの零化を与える。

## 方針

核と余核の零化から逆向きの写像を作る一般補題（`exists_scalar_inverse_of_ker_coker_annihilated`）を本体にし、有限自由を経由する分解はその特殊例として導く。

## 規約

冪ねじれの仮定は `Module.IsTorsionBy` にそろえる。

## 使われ方

CLMST の Prop 2.4.7（同種写像の降下）、Paper。
-/

@[expose] public noncomputable section

universe u v w

section ScalarIsogenyInversePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- Kernel and cokernel annihilators give a two-sided scalar inverse for the actual map.
Neither module is required to be finite, projective, free, or complete. -/
theorem exists_scalar_inverse_of_ker_coker_annihilated
    (f : M →ₗ[R] N) (a b : R)
    (hk : ∀ x : f.ker, a • x = 0)
    (hc : ∀ y : N ⧸ f.range, b • y = 0) :
    ∃ v : N →ₗ[R] M,
      v.comp f = (a * b) • LinearMap.id ∧ f.comp v = (a * b) • LinearMap.id := by
  have hker : f.ker ≤ LinearMap.ker (a • (LinearMap.id : M →ₗ[R] M)) := by
    intro x hx
    have hh := congrArg (fun z : f.ker => (z : M)) (hk ⟨x, hx⟩)
    exact hh
  let u : M ⧸ f.ker →ₗ[R] M := f.ker.liftQ (a • LinearMap.id) hker
  let v₀ : f.range →ₗ[R] M := u.comp f.quotKerEquivRange.symm.toLinearMap
  have hv₀ (x : M) : v₀ (f.rangeRestrict x) = a • x := by
    change u (f.quotKerEquivRange.symm ⟨f x, f.mem_range_self x⟩) = a • x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hfv (y : f.range) : f (v₀ y) = a • (y : N) := by
    obtain ⟨x, hx⟩ := y.property
    have he : f.rangeRestrict x = y := Subtype.ext hx
    rw [← he, hv₀, map_smul]
    rfl
  have hmem (y : N) : b • y ∈ f.range := by
    apply (Submodule.Quotient.mk_eq_zero f.range).mp
    change f.range.mkQ (b • y) = 0
    rw [map_smul]
    exact hc _
  let w : N →ₗ[R] f.range := (b • LinearMap.id).codRestrict f.range hmem
  let v : N →ₗ[R] M := v₀.comp w
  refine ⟨v, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change v₀ (b • f.rangeRestrict x) = (a * b) • x
    rw [map_smul, hv₀, smul_smul, mul_comm]
  · apply LinearMap.ext
    intro y
    change f (v₀ (w y)) = (a * b) • y
    rw [hfv]
    change a • (b • y) = (a * b) • y
    rw [smul_smul]

end SerrePositivity

end ScalarIsogenyInversePart

section ScalarIsogenyTensorPart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) (T : Type v) (M : Type w) [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M]

/-- 元の R→T の核・余核の零化から、元の M→T⊗R M の両側スカラー逆を作る。 -/
theorem exists_tensor_unit_scalar_inverse_of_ker_coker_annihilated
    (a b : R)
    (hk : ∀ x : (Algebra.linearMap R T).ker, a • x = 0)
    (hc : ∀ y : T ⧸ (Algebra.linearMap R T).range, b • y = 0) :
    let u := TensorProduct.mk R T M (1 : T)
    ∃ w : T ⊗[R] M →ₗ[R] M,
      w.comp u = (a * b) • LinearMap.id ∧ u.comp w = (a * b) • LinearMap.id := by
  let u := TensorProduct.mk R T M (1 : T)
  obtain ⟨v, hv, hf⟩ := exists_scalar_inverse_of_ker_coker_annihilated
    (Algebra.linearMap R T) a b hk hc
  let w : T ⊗[R] M →ₗ[R] M :=
    (TensorProduct.lid R M).toLinearMap.comp (LinearMap.rTensor M v)
  have hw (t : T) (m : M) : w (t ⊗ₜ[R] m) = v t • m := by
    change (TensorProduct.lid R M) (LinearMap.rTensor M v (t ⊗ₜ[R] m)) = v t • m
    rw [LinearMap.rTensor_tmul]
    exact TensorProduct.lid_tmul m (v t)
  have hv1 : v (1 : T) = a * b := by
    have h := LinearMap.congr_fun hv 1
    change v (algebraMap R T 1) = (a * b) • (1 : R) at h
    simpa only [map_one, smul_eq_mul, mul_one] using h
  refine ⟨w, ?_, ?_⟩
  · ext m
    change w ((1 : T) ⊗ₜ[R] m) = (a * b) • m
    rw [hw, hv1]
  · apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t m =>
        change (1 : T) ⊗ₜ[R] w (t ⊗ₜ[R] m) = (a * b) • (t ⊗ₜ[R] m)
        rw [hw]
        have hft : algebraMap R T (v t) = (a * b) • t := LinearMap.congr_fun hf t
        calc
          (1 : T) ⊗ₜ[R] (v t • m) = ((v t : R) • (1 : T)) ⊗ₜ[R] m :=
            (TensorProduct.smul_tmul _ _ _).symm
          _ = algebraMap R T (v t) ⊗ₜ[R] m := by rw [Algebra.smul_def, mul_one]
          _ = ((a * b) • t) ⊗ₜ[R] m := by rw [hft]
          _ = (a * b) • (t ⊗ₜ[R] m) := (TensorProduct.smul_tmul' _ _ _).symm
    | add x y hx hy =>
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
          map_add, smul_add, hx, hy]

/-- 同じスカラー積が、元の通常 tensor の単位の核・余核をともに消す。 -/
theorem tensor_unit_ker_coker_annihilated
    (a b : R)
    (hk : ∀ x : (Algebra.linearMap R T).ker, a • x = 0)
    (hc : ∀ y : T ⧸ (Algebra.linearMap R T).range, b • y = 0) :
    let u := TensorProduct.mk R T M (1 : T)
    (∀ x : u.ker, (a * b) • x = 0) ∧
      (∀ y : (T ⊗[R] M) ⧸ u.range, (a * b) • y = 0) := by
  let u := TensorProduct.mk R T M (1 : T)
  obtain ⟨w, hw, hu⟩ :=
    exists_tensor_unit_scalar_inverse_of_ker_coker_annihilated R T M a b hk hc
  constructor
  · intro x
    apply Subtype.ext
    have h := LinearMap.congr_fun hw (x : M)
    change w (u (x : M)) = (a * b) • (x : M) at h
    rw [x.property, map_zero] at h
    exact h.symm
  · intro y
    obtain ⟨y, rfl⟩ := u.range.mkQ_surjective y
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero u.range).mpr
    exact ⟨w y, LinearMap.congr_fun hu y⟩

end SerrePositivity

end ScalarIsogenyTensorPart

section FiniteFreeScalarFactorizationPart

namespace SerrePositivity
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- A scalar killing the cokernel lifts its action on the finite free target. -/
lemma exists_finiteFree_scalar_lift (r : ℕ) (f : M →ₗ[R] (Fin r → R)) (a : R)
    (ha : ∀ y : (Fin r → R) ⧸ f.range, a • y = 0) :
    ∃ v : (Fin r → R) →ₗ[R] M, f.comp v = a • LinearMap.id := by
  classical
  let b := Pi.basisFun R (Fin r)
  have hmem (j : Fin r) : a • b j ∈ f.range := by
    apply (Submodule.Quotient.mk_eq_zero f.range).mp
    change f.range.mkQ (a • b j) = 0
    rw [map_smul]
    exact ha _
  choose z hz using fun j : Fin r => hmem j
  let v := b.constr R z
  refine ⟨v, ?_⟩
  apply b.ext
  intro j
  change f (v (b j)) = a • b j
  rw [show v (b j) = z j from b.constr_basis R _ j]
  exact hz j

/-- The product of kernel and cokernel annihilators factors through the same finite free module.
The source need not be finite, reduced, or torsion free. -/
lemma exists_scalar_factorization_through_finiteFree
    (r : ℕ) (f : M →ₗ[R] (Fin r → R)) (a b : R)
    (ha : ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hb : ∀ x : f.ker, b • x = 0) :
    ∃ v : (Fin r → R) →ₗ[R] M, v.comp f = (a * b) • LinearMap.id := by
  obtain ⟨v, hv⟩ := exists_finiteFree_scalar_lift r f a ha
  refine ⟨b • v, ?_⟩
  apply LinearMap.ext
  intro x
  have hker : v (f x) - a • x ∈ f.ker := by
    change f (v (f x) - a • x) = 0
    rw [map_sub, map_smul]
    have h := LinearMap.congr_fun hv (f x)
    change f (v (f x)) = a • f x at h
    rw [h, sub_self]
  have h := congrArg (fun z : f.ker => (z : M)) (hb ⟨v (f x) - a • x, hker⟩)
  change b • (v (f x) - a • x) = 0 at h
  rw [smul_sub, sub_eq_zero] at h
  change b • v (f x) = (a * b) • x
  simpa only [smul_smul, mul_comm] using h

end SerrePositivity

end FiniteFreeScalarFactorizationPart

section FiniteProductIsogenyPart

namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 有限個の成分ごとの指数を、実直積写像の核・余核の同じ一つの指数へまとめる。 -/
theorem exists_uniform_pow_ker_coker_piMap
    {ι : Type*} [Finite ι] {R : Type u} [CommRing R]
    {M N : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) (g : R)
    (h : ∀ i, ∃ n : ℕ,
      (∀ x : (f i).ker, g ^ n • x = 0) ∧
        (∀ y : (N i) ⧸ (f i).range, g ^ n • y = 0)) :
    ∃ n : ℕ, (∀ x : (LinearMap.piMap f).ker, g ^ n • x = 0) ∧
      (∀ y : ((i : ι) → N i) ⧸ (LinearMap.piMap f).range, g ^ n • y = 0) := by
  classical
  letI := Fintype.ofFinite ι
  choose n hn using h
  let k := Finset.univ.sup n
  have hle (i : ι) : n i ≤ k := Finset.le_sup (Finset.mem_univ i)
  have hk (i : ι) (x : (f i).ker) : g ^ k • x = 0 := by
    rw [show k = (k - n i) + n i from (Nat.sub_add_cancel (hle i)).symm,
      pow_add, mul_smul, (hn i).1 x, smul_zero]
  have hc (i : ι) (y : (N i) ⧸ (f i).range) : g ^ k • y = 0 := by
    rw [show k = (k - n i) + n i from (Nat.sub_add_cancel (hle i)).symm,
      pow_add, mul_smul, (hn i).2 y, smul_zero]
  refine ⟨k, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change g ^ k • (x : (i : ι) → M i) = 0
    ext i
    have hi : f i (x.1 i) = 0 := congrFun x.property i
    exact congrArg Subtype.val (hk i ⟨x.1 i, hi⟩)
  · intro y
    obtain ⟨y, rfl⟩ := (LinearMap.piMap f).range.mkQ_surjective y
    have hm (i : ι) : g ^ k • y i ∈ (f i).range := by
      apply (Submodule.Quotient.mk_eq_zero (f i).range).mp
      exact ((f i).range.mkQ.map_smul (g ^ k) (y i)).trans (hc i _)
    choose x hx using hm
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.piMap f).range).mpr
    exact ⟨x, funext hx⟩

end SerrePositivity

end FiniteProductIsogenyPart

section ReducedFiniteFreeIsogenyPart

namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 被約環ではg冪ねじれの元をg自身が消す。 -/
theorem mul_eq_zero_of_pow_mul_eq_zero [IsReduced R] (g a : R)
    (h : ∃ n : ℕ, g ^ n * a = 0) : g * a = 0 := by
  obtain ⟨n, hn⟩ := h
  apply IsReduced.eq_zero
  refine ⟨n + 1, ?_⟩
  calc
    (g * a) ^ (n + 1) = (g ^ n * a) * (g * a ^ n) := by ring
    _ = 0 := by rw [hn, zero_mul]

/-- 自由加群の局所化で零になる元をg自身が消す。 -/
theorem smul_eq_zero_of_free_localized_zero [IsReduced R] (g : R) (r : ℕ)
    (y : Fin r → R)
    (hy : LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin r → R) y = 0) :
    g • y = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_smul_zero_of_localized_zero g y hy
  ext i
  exact mul_eq_zero_of_pow_mul_eq_zero g (y i) ⟨n, congrFun hn i⟩

/-- 有限自由加群への局所化同型の核・余核は一様なg冪で消える。
核の有限生成性も、RのNoether性も仮定しない。 -/
theorem exists_pow_ker_coker_annihilator [IsReduced R] [Module.Finite R M]
    (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ a b : ℕ, (∀ x : M, f x = 0 → g ^ a • x = 0) ∧
      (∀ y : (Fin r → R) ⧸ LinearMap.range f, g ^ b • y = 0) := by
  obtain ⟨k, ψ, _, hψ⟩ := exists_away_inverse g r f hf
  obtain ⟨b, hb⟩ := exists_uniform_pow_smul_coker_zero_of_away_surjective g f hf.surjective
  obtain ⟨c, hc⟩ := exists_uniform_pow_smul_coker_zero_of_away_surjective g ψ hψ.surjective
  refine ⟨c + 1, b, ?_, hb⟩
  intro x hx
  have hmem : g ^ c • x ∈ LinearMap.range ψ := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact (map_smul (LinearMap.range ψ).mkQ (g ^ c) x).trans (hc _)
  obtain ⟨y, hy⟩ := hmem
  have hcomp : f (ψ y) = 0 := by rw [hy, map_smul, hx, smul_zero]
  let ιF := LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin r → R)
  have hzero : ιF y = 0 := by
    apply hψ.injective
    apply hf.injective
    simp only [map_zero, awayModuleMap, ιF, IsLocalizedModule.map_apply, hcomp]
  have hgy := smul_eq_zero_of_free_localized_zero g r y hzero
  calc
    g ^ (c + 1) • x = g • (g ^ c • x) := by rw [pow_succ', mul_smul]
    _ = ψ (g • y) := by rw [map_smul, hy]
    _ = 0 := by rw [hgy, map_zero]

end SerrePositivity

end ReducedFiniteFreeIsogenyPart

section FinitePresentationIsogenyLiftPart

namespace SerrePositivity
variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M]

/-- 局所化同型の共通分母を払い、局所化すると全単射となる元の加群写像を得る。 -/
theorem exists_away_comparison_of_finitePresentation (g : R)
    (e : LocalizedModule (Submonoid.powers g) M ≃ₗ[R]
      LocalizedModule (Submonoid.powers g) N) :
    ∃ (k : ℕ) (f : M →ₗ[R] N),
      awayModuleMap g f = g ^ k • e.toLinearMap ∧ Function.Bijective (awayModuleMap g f) := by
  let S := Submonoid.powers g
  let ιM := LocalizedModule.mkLinearMap S M
  let ιN := LocalizedModule.mkLinearMap S N
  obtain ⟨f, s, hf⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S ιN
    (e.toLinearMap.comp ιM)
  have hmap : awayModuleMap g f = (s : R) • e.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S ιM ιN
    change (IsLocalizedModule.map S ιM ιN f).comp ιM =
      ((s : R) • e.toLinearMap).comp ιM
    rw [IsLocalizedModule.map_comp]
    simpa only [Submonoid.smul_def, LinearMap.smul_comp] using hf
  obtain ⟨k, hk⟩ := s.property
  refine ⟨k, f, ?_, ?_⟩
  · simpa only [hk] using hmap
  · rw [hmap]
    exact ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units ιN s)).comp e.bijective

end SerrePositivity

end FinitePresentationIsogenyLiftPart

section PullbackAnnihilatorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits

/-- The concrete fiber-product algebra is the categorical ring pullback. -/
theorem algHom_isPullback_pullback
    {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D]
    (r : B →ₐ[R] D) (b : C →ₐ[R] D) :
    IsPullback (CommRingCat.ofHom (AlgHom.pullbackFst r b).toRingHom)
      (CommRingCat.ofHom (AlgHom.pullbackSnd r b).toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom) := by
  letI : ReflectsLimit
      (cospan (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
      (forget CommRingCat) := reflectsLimit_of_reflectsIsomorphisms _ _
  have hcomm : CommRingCat.ofHom (AlgHom.pullbackFst r b).toRingHom ≫
      CommRingCat.ofHom r.toRingHom =
      CommRingCat.ofHom (AlgHom.pullbackSnd r b).toRingHom ≫ CommRingCat.ofHom b.toRingHom := by
    ext x
    exact x.property
  apply (IsPullback.map_iff (forget CommRingCat) hcomm).mp
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact x.property
  · intro x y h
    exact Subtype.ext (Prod.ext h.1 h.2)
  · intro x y h
    exact ⟨⟨(x, y), h⟩, rfl, rfl⟩

/-- A scalar killing both bottom objects of a pullback square kills the kernel
and cokernel of its top horizontal linear map. -/
theorem linearMap_ker_coker_annihilated_of_type_isPullback
    {R M N P Q : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) (l : M →ₗ[R] P) (r : N →ₗ[R] Q) (b : P →ₗ[R] Q)
    (hPB : IsPullback (↾f : M ⟶ N) (↾l : M ⟶ P) (↾r : N ⟶ Q) (↾b : P ⟶ Q))
    (a : R) (hP : ∀ x : P, a • x = 0) (hQ : ∀ y : Q, a • y = 0) :
    (∀ x : f.ker, a • x = 0) ∧ (∀ y : N ⧸ f.range, a • y = 0) := by
  constructor
  · intro x
    apply Subtype.ext
    change a • (x : M) = 0
    apply Types.ext_of_isPullback hPB
    · change f (a • (x : M)) = f 0
      rw [map_smul, x.property, smul_zero, map_zero]
    · change l (a • (x : M)) = l 0
      rw [map_smul, map_zero]
      exact hP _
  · intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro z
    have hz : r (a • z) = b 0 := by
      rw [map_smul, map_zero]
      exact hQ _
    obtain ⟨x, hx, _⟩ := Types.exists_of_isPullback hPB (a • z) 0 hz
    exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨x, hx⟩

/-- A scalar vanishing in the bottom-left algebra of an actual ring pullback
annihilates the kernel and cokernel over the original scalar ring. -/
theorem algHom_ker_coker_annihilated_of_isPullback
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hPB : IsPullback (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom l.toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (a : R) (ha : algebraMap R C a = 0) :
    (∀ x : f.toLinearMap.ker, a • x = 0) ∧
      (∀ y : B ⧸ f.toLinearMap.range, a • y = 0) := by
  have hPB' : IsPullback (↾f : A ⟶ B) (↾l : A ⟶ C) (↾r : B ⟶ D) (↾b : C ⟶ D) :=
    hPB.map (forget CommRingCat)
  have hb : algebraMap R D a = 0 := by
    rw [← b.commutes, ha, map_zero]
  apply linearMap_ker_coker_annihilated_of_type_isPullback
    f.toLinearMap l.toLinearMap r.toLinearMap b.toLinearMap hPB' a
  · intro x
    rw [Algebra.smul_def, ha, zero_mul]
  · intro y
    rw [Algebra.smul_def, hb, zero_mul]

end SerrePositivity

end PullbackAnnihilatorPart
