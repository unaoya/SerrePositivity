module

public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # 等標数の有限段から底への Frobenius

## 概要

標数 p の環 A 上の有限段から A への Frobenius 写像 `towerStageFrobenius`（係数 a を a^(p^n)、付加した根を元のパラメータへ送る）を作り、その p^n 乗が元の元であることと単射性を示す。A が完備な Noether 局所環で剰余体が完全、有限段が被約なら全射で、環同型 `towerStageFrobeniusEquiv` になる。

## 方針

写像は多項式環からの `eval₂Hom (iterateFrobenius A p n) t` を商へ降ろして作る。全射性は剰余体の完全性と完備性による逐次近似。

## 規約

環同型は A の作用を Frobenius でねじるので A 代数同型ではない。名前空間は `SerrePositivity.Section2`。

## 使われ方

論文の定理 2.5 の等標数の場合（Paper/Section2 の PerfectApproximation・PerfectBaseChange・PerfectConductor・PerfectKoszulLength）。
-/

@[expose] public noncomputable section

universe u

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
