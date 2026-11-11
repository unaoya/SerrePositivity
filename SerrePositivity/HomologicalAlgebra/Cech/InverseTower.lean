module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# 全射的な逆塔の余鎖完全性

## 概要
各段で完全な余鎖複体の塔が各次数で全射的なら、その次数ごとの逆極限も完全。

## 方針
隣接段で原像を境界によって修正し、両立する原像を帰納的に作る。

## 規約
自然数次数。増大項を次数 0 に含める。

## 使われ方
BS 著者版 Corollary 3.12 (c) の有限剰余からの逆極限。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace SerrePositivity.Cech

open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCompletion

variable {R : Type v} [CommRing R]

private theorem cochain_acyclic_iff (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    K.Acyclic ↔ Function.Injective (K.d 0 1) ∧
      ∀ j : ℕ, Function.Exact (K.d j (j + 1)) (K.d (j + 1) (j + 2)) := by
  have h₀ : K.ExactAt 0 ↔ Function.Injective (K.d 0 1) := by
    rw [K.exactAt_iff' 0 0 1 (by simp) (by simp),
      ShortComplex.exact_iff_mono _ (K.shape 0 0 (by simp)),
      ModuleCat.mono_iff_injective]
    rfl
  have hs (j : ℕ) : K.ExactAt (j + 1) ↔ Function.Exact (K.d j (j + 1)) (K.d (j + 1) (j + 2)) := by
    rw [K.exactAt_iff' j (j + 1) (j + 2) (by simp) (by simp),
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    rfl
  exact ⟨fun h ↦ ⟨h₀.mp (h 0), fun j ↦ (hs j).mp (h (j + 1))⟩, fun h j ↦
    Nat.casesOn j (h₀.mpr h.1) (fun j ↦ (hs j).mpr (h.2 j))⟩

/-- 概要：次数ごとの逆極限が全射的な完全複体の塔で計算できれば、複体は完全。
方針：隣接段の原像を境界で修正し、極限で原像を取る。
規約：増大を第零項に含めた自然数次数。
使われ方：忠実平坦な有限剰余の増大 Čech 完全性を完備な複体へ移す。 -/
theorem acyclic_of_degreewise_surjective_tower
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℕ)
    (t : ∀ n, K (n + 1) ⟶ K n) (f : ∀ n, C ⟶ K n)
    (hf : ∀ n, f (n + 1) ≫ t n = f n)
    (ht : ∀ n j, Function.Surjective ((t n).f j))
    (hK : ∀ n, (K n).Acyclic)
    (hlim : ∀ j,
      let M (n : ℕ) : Type u := (K n).X j
      let s (n : ℕ) : M (n + 1) →ₗ[R] M n := ((t n).f j).hom
      Function.Bijective
        (moduleTowerLimitLift R M s (C.X j) (fun n ↦ ((f n).f j).hom)
          (fun n ↦ congrArg (fun g : C ⟶ K n ↦ (g.f j).hom) (hf n)))) : C.Acyclic := by
  have htcomp (n j : ℕ) (x : (K (n + 1)).X j) :
      (t n).f (j + 1) ((K (n + 1)).d j (j + 1) x) =
        (K n).d j (j + 1) ((t n).f j x) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((t n).comm j (j + 1)).symm) x
  have hfcomp (n j : ℕ) (x : C.X j) :
      (f n).f (j + 1) (C.d j (j + 1) x) = (K n).d j (j + 1) ((f n).f j x) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((f n).comm j (j + 1)).symm) x
  have hfcompat (n j : ℕ) (x : C.X j) : (t n).f j ((f (n + 1)).f j x) = (f n).f j x :=
    DFunLike.congr_fun (congrArg (fun g : C ⟶ K n ↦ (g.f j).hom) (hf n)) x
  have he (n : ℕ) := (cochain_acyclic_iff (K n)).mp (hK n)
  apply (cochain_acyclic_iff C).mpr
  refine ⟨?_, fun j x ↦ ⟨?_, ?_⟩⟩
  · intro x y hxy
    apply (hlim 0).injective
    apply Subtype.ext
    funext n
    change (f n).f 0 x = (f n).f 0 y
    apply (he n).1
    rw [← hfcomp, ← hfcomp, hxy]
  · intro hx
    let S (n : ℕ) := {y : (K n).X j // (K n).d j (j + 1) y = (f n).f (j + 1) x}
    have hS (n : ℕ) : Nonempty (S n) := by
      have hzero : (K n).d (j + 1) (j + 2) ((f n).f (j + 1) x) = 0 := by
        rw [← hfcomp, hx, map_zero]
      obtain ⟨y, hy⟩ := ((he n).2 j _).mp hzero
      exact ⟨⟨y, hy⟩⟩
    have hstep (n : ℕ) (y : S n) : ∃ z : S (n + 1), (t n).f j z = y := by
      let z := (hS (n + 1)).some
      let δ := (t n).f j z - (y : (K n).X j)
      have hδ : (K n).d j (j + 1) δ = 0 := by
        dsimp only [δ]
        rw [map_sub, ← htcomp, z.property, hfcompat, y.property, sub_self]
      cases j with
      | zero =>
        have hzero : δ = 0 := (he n).1 (by rw [hδ, map_zero])
        exact ⟨z, sub_eq_zero.mp hzero⟩
      | succ j =>
        obtain ⟨v, hv⟩ := ((he n).2 j δ).mp hδ
        obtain ⟨w, hw⟩ := ht n j v
        let z' : (K (n + 1)).X (j + 1) := z - (K (n + 1)).d j (j + 1) w
        refine ⟨⟨z', ?_⟩, ?_⟩
        · change (K (n + 1)).d (j + 1) (j + 2) (z - (K (n + 1)).d j (j + 1) w) = _
          rw [map_sub, z.property]
          have hh := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
            ((K (n + 1)).d_comp_d j (j + 1) (j + 2))) w
          exact sub_eq_self.mpr hh
        · change (t n).f (j + 1) (z - (K (n + 1)).d j (j + 1) w) = _
          rw [map_sub, htcomp, hw, hv]
          exact sub_sub_cancel _ _
    let y (n : ℕ) : S n := Nat.rec (motive := S) (hS 0).some
      (fun n z ↦ (hstep n z).choose) n
    have hy (n : ℕ) : (t n).f j (y (n + 1)) = (y n : (K n).X j) :=
      (hstep n (y n)).choose_spec
    let yl : moduleTowerLimit R (fun n ↦ (K n).X j) (fun n ↦ ((t n).f j).hom) :=
      ⟨fun n ↦ y n, (mem_moduleTowerLimit_iff R _ _ _).mpr hy⟩
    obtain ⟨y', hy'⟩ := (hlim j).surjective yl
    refine ⟨y', (hlim (j + 1)).injective ?_⟩
    apply Subtype.ext
    funext n
    have h : (f n).f j y' = y n := congrArg (fun z ↦ z.val n) hy'
    change (f n).f (j + 1) (C.d j (j + 1) y') = (f n).f (j + 1) x
    rw [hfcomp, h, (y n).property]
  · rintro ⟨y, rfl⟩
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (C.d_comp_d j (j + 1) (j + 2))) y

section DegreewiseLimit

variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℕ) (t : ∀ n, K (n + 1) ⟶ K n)

private abbrev termLimit (j : ℕ) :=
  moduleTowerLimit R (fun n ↦ (K n).X j) (fun n ↦ ((t n).f j).hom)

private def limitDifferential (j : ℕ) : termLimit K t j →ₗ[R] termLimit K t (j + 1) where
  toFun x := ⟨fun n ↦ (K n).d j (j + 1) (x.val n), (mem_moduleTowerLimit_iff R _ _ _).mpr
    (fun n ↦ by
      have h : (t n).f (j + 1) ((K (n + 1)).d j (j + 1) (x.val (n + 1))) =
          (K n).d j (j + 1) ((t n).f j (x.val (n + 1))) :=
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((t n).comm j (j + 1)).symm)
          (x.val (n + 1))
      change (t n).f (j + 1) ((K (n + 1)).d j (j + 1) (x.val (n + 1))) =
        (K n).d j (j + 1) (x.val n)
      rw [h, (mem_moduleTowerLimit_iff R _ _ _).mp x.property n])⟩
  map_add' x y := Subtype.ext (funext fun n ↦ map_add ((K n).d j (j + 1)).hom _ _)
  map_smul' r x := Subtype.ext (funext fun n ↦ map_smul ((K n).d j (j + 1)).hom _ _)

/-- 次数ごとに両立する元を取る余鎖複体。 -/
def degreewiseTowerLimit : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun j ↦ ModuleCat.of R (termLimit K t j))
    (fun j ↦ ModuleCat.ofHom (limitDifferential K t j)) (fun j ↦ by
      ext x n
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((K n).d_comp_d j (j + 1) (j + 2)))
        (x.val n))

/-- 次数ごとの逆極限から各段への射影。 -/
def degreewiseTowerProjection (n : ℕ) : degreewiseTowerLimit K t ⟶ K n :=
  CochainComplex.ofHom (fun j ↦ ModuleCat.ofHom (moduleTowerProjection R _ _ n)) (fun j ↦ by
    have hd : (degreewiseTowerLimit K t).d j (j + 1) =
        ModuleCat.ofHom (limitDifferential K t j) := by
      change CochainComplex.of.d (fun j ↦ ModuleCat.of R (termLimit K t j))
        (fun j ↦ ModuleCat.ofHom (limitDifferential K t j)) j (j + 1) = _
      exact CochainComplex.of_d _ _ j
    rw [hd]
    rfl)

/-- 次数ごとの全射的な塔について、完全性は逆極限で保たれる。 -/
theorem degreewiseTowerLimit_acyclic (ht : ∀ n j, Function.Surjective ((t n).f j))
    (hK : ∀ n, (K n).Acyclic) : (degreewiseTowerLimit K t).Acyclic := by
  have hf (n : ℕ) : degreewiseTowerProjection K t (n + 1) ≫ t n =
      degreewiseTowerProjection K t n := by
    ext j x
    exact (mem_moduleTowerLimit_iff R _ _ _).mp x.property n
  apply acyclic_of_degreewise_surjective_tower _ K t (degreewiseTowerProjection K t) hf ht hK
  intro j
  exact Function.bijective_id

end DegreewiseLimit

end SerrePositivity.Cech
