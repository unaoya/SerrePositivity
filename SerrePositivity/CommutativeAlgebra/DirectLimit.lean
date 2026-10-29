module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # 有向直極限の平坦性と局所性

## 概要

非空な有向集合で添字づけられた系について、次を示す。
- 平坦加群の有向直極限は平坦（`directLimit_flat`、標準モデル `Module.DirectLimit` 版は
  `moduleDirectLimit_flat`）。遷移写像の単射性は要らない。
- 局所環の有向直極限は局所環（`directLimit_isLocalRing`）。遷移写像の局所性は要らない。
  遷移写像が局所なら、各段からの標準写像も局所（`directLimit_isLocalHom`）。

## 方針

平坦性：有限個の元を一つの段へ持ち上げ（`directLimit_exists_representatives`）、零関係が後続の段で
成立することを使って、Mathlib の平坦性の方程式判定（`Module.Flat.of_forall_isTrivialRelation`）を適用する。
局所性：直極限で単元になる元は、ある後続の段で既に単元である（`directLimit_isUnit_iff`）。
`x + y = 1` を一つの段へ持ち上げ、その段の局所性を使う。

## 規約

遷移写像は `FunLike` の一般の族（`DirectLimit` の一般形）で扱う。環の Noether 性は使わない。
最新の Mathlib には局所環の filtered colimit の局所性（`CommRingCat.FilteredColimits`）があるが、
遷移写像の局所性を仮定する。平坦性は Mathlib に無い。Mathlib への提出候補（mathlib-upstream の G6）。

## 使われ方

剰余体拡大の構成の極限段（`ResidueFieldDirectLimit`）、完全多項式環の平坦性（`PerfectPolynomialFlat`）、
André の補題の超限構成（BhattScholze）。
-/

public section

namespace SerrePositivity

section Flat

variable {R ι : Type*} [CommRing R] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable [∀ i j (h : i ≤ j), FunLike (T h) (M i) (M j)]
variable [∀ i j (h : i ≤ j), LinearMapClass (T h) R (M i) (M j)]
variable (f : ∀ i j (h : i ≤ j), T h) [DirectedSystem M (f · · ·)]

/-- 直極限の有限個の元には、共通の段での代表元が存在する。 -/
theorem directLimit_exists_representatives {n : ℕ} (x : Fin n → DirectLimit M f) :
    ∃ i, ∃ y : Fin n → M i, ∀ a, DirectLimit.Module.of R ι M f i (y a) = x a := by
  classical
  induction n with
  | zero =>
    exact ⟨Classical.arbitrary ι, Fin.elim0, fun a ↦ Fin.elim0 a⟩
  | succ n ih =>
    obtain ⟨i, y, hy⟩ := ih (fun a ↦ x a.castSucc)
    obtain ⟨j, z, hz⟩ := DirectLimit.exists_eq_mk f (x (Fin.last n))
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, Fin.lastCases (f j k hjk z) (fun a ↦ f i k hik (y a)), ?_⟩
    intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · simp only [Fin.lastCases_last, DirectLimit.Module.of_f]
      with_unfolding_all exact hz.symm
    · simpa only [Fin.lastCases_castSucc, DirectLimit.Module.of_f] using hy b

/-- 有向直極限の各段が平坦なら、直極限も平坦である。
遷移写像の単射性・有限生成性は要求しない。 -/
theorem directLimit_flat [∀ i, Module.Flat R (M i)] : Module.Flat R (DirectLimit M f) := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro n c x hx
  obtain ⟨i, y, hy⟩ := directLimit_exists_representatives M f x
  have hzero : DirectLimit.Module.of R ι M f i (∑ a, c a • y a) = 0 := by
    simpa only [map_sum, map_smul, hy] using hx
  obtain ⟨j, hij, hj⟩ := (DirectLimit.exists_eq_zero (f := f) ⟨i, ∑ a, c a • y a⟩).mp hzero
  have hrel : ∑ a, c a • f i j hij (y a) = 0 := by
    simpa only [map_sum, map_smul] using hj
  obtain ⟨k, A, z, hz, hA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k, A, fun b ↦ DirectLimit.Module.of R ι M f j (z b), ?_, hA⟩
  intro a
  have h := congrArg (DirectLimit.Module.of R ι M f j) (hz a)
  simpa only [map_sum, map_smul, DirectLimit.Module.of_f, hy] using h

end Flat

section ModuleFlat

variable {R ι : Type*} [CommRing R] [Preorder ι] [DecidableEq ι]
variable [IsDirectedOrder ι] [Nonempty ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) [DirectedSystem M (f · · ·)]

/-- A directed limit of flat modules is flat, in the standard `Module.DirectLimit` model. -/
theorem moduleDirectLimit_flat [∀ i, Module.Flat R (M i)] :
    Module.Flat R (Module.DirectLimit M f) := by
  have := directLimit_flat M f
  exact Module.Flat.of_linearEquiv (Module.DirectLimit.linearEquiv M f)

end ModuleFlat

section LocalRing

open IsLocalRing
variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (S : ι → Type*) [∀ i, CommRing (S i)]
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable [∀ i j (h : i ≤ j), FunLike (T h) (S i) (S j)]
variable [∀ i j (h : i ≤ j), RingHomClass (T h) (S i) (S j)]
variable (f : ∀ i j (h : i ≤ j), T h) [DirectedSystem S (f · · ·)]

/-- 直極限で単元になる元は、ある後続段で既に単元になる。 -/
theorem directLimit_isUnit_iff (i : ι) (x : S i) :
    IsUnit (DirectLimit.Ring.of S f i x) ↔ ∃ j, ∃ h : i ≤ j, IsUnit (f i j h x) := by
  constructor
  · intro hx
    obtain ⟨y, hxy⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨k, z, hz⟩ := DirectLimit.exists_eq_mk f y
    rw [hz] at hxy
    obtain ⟨j, hij, hkj⟩ := exists_ge_ge i k
    have hm : DirectLimit.Ring.of S f j (f i j hij x * f k j hkj z) = 1 := by
      rw [map_mul, DirectLimit.Ring.of_f, DirectLimit.Ring.of_f]
      exact hxy
    obtain ⟨l, hjl, hl⟩ := (DirectLimit.exists_eq_one (f := f)
      ⟨j, f i j hij x * f k j hkj z⟩).mp hm
    refine ⟨l, hij.trans hjl, isUnit_iff_exists_inv.mpr ⟨f j l hjl (f k j hkj z), ?_⟩⟩
    simpa only [map_mul, DirectedSystem.map_map'] using hl
  · rintro ⟨j, hij, hx⟩
    rw [← DirectLimit.Ring.of_f (G := S) (f := f) hij x]
    exact hx.map (DirectLimit.Ring.of S f j)

/-- 局所環の非空有向直極限は局所環である。遷移写像の局所性は不要。 -/
theorem directLimit_isLocalRing [∀ i, IsLocalRing (S i)] :
    IsLocalRing (DirectLimit S f) := by
  refine ⟨fun {x y} h ↦ ?_⟩
  obtain ⟨i, a, b, ha, hb⟩ := DirectLimit.exists_eq_mk₂ f x y
  have ha' : DirectLimit.Ring.of S f i a = x := by with_unfolding_all exact ha.symm
  have hb' : DirectLimit.Ring.of S f i b = y := by with_unfolding_all exact hb.symm
  have hab : DirectLimit.Ring.of S f i (a + b) = 1 := by
    rw [map_add, ha', hb']
    exact h
  obtain ⟨j, hij, hj⟩ := (DirectLimit.exists_eq_one (f := f) ⟨i, a + b⟩).mp hab
  have hu := IsLocalRing.isUnit_or_isUnit_of_add_one (by simpa only [map_add] using hj)
  exact hu.imp (fun hunit ↦ ha' ▸ (directLimit_isUnit_iff S f i a).mpr ⟨j, hij, hunit⟩)
    (fun hunit ↦ hb' ▸ (directLimit_isUnit_iff S f i b).mpr ⟨j, hij, hunit⟩)

/-- 遷移写像が局所なら、各段から直極限への標準写像も局所である。 -/
theorem directLimit_isLocalHom
    (hlocal : ∀ i j h, IsLocalHom (RingHomClass.toRingHom (f i j h))) (i : ι) :
    IsLocalHom (DirectLimit.Ring.of S f i) := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨j, hij, hj⟩ := (directLimit_isUnit_iff S f i x).mp hx
  let : IsLocalHom (RingHomClass.toRingHom (f i j hij)) := hlocal i j hij
  exact isUnit_of_map_unit (RingHomClass.toRingHom (f i j hij)) x hj

end LocalRing

end SerrePositivity
