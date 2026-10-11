module

public import SerrePositivity.Paper.Section2.TowerLengthOn
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import SerrePositivity.CommutativeAlgebra.KoszulFiniteLength

/-! # 根の塔の `p` 進完備化と正規化長さ

CLMST §2.2 の完備化上の長さは、完備化前の塔への係数制限で測る。
`A → Λ → R∞ → C` の作用が両立すれば、直接 `Λ` へ制限した加群と、
`R∞` を経由して制限した加群は線形同型なので、長さが一致する。
さらに、有限局所包含 `A → D` について `m_A D ⊆ m_D` を使い、
パラメータ系の Koszul ホモロジーに一様な `m_A` の消去冪を供給する。
ここでは perfectoid 性やホモロジー消滅を仮定しない。
混標数の CLMST の引用を適用するために `MixedLengthAlgebra` から使う。
-/

@[expose] public section
universe u
open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 標準的な根の塔の `p` 進完備化。 -/
abbrev CompletedTower :=
  AdicCompletion (Ideal.span {(p : Tower A t p)}) (Tower A t p)

/-- 基底環と塔の作用は、完備化への標準写像と両立する。 -/
instance : IsScalarTower A (Tower A t p) (CompletedTower A t p) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable [IsLocalRing A]

/-- 完備化した塔における `m_A` の拡大。 -/
noncomputable def completedTowerMaxIdeal : Ideal (CompletedTower A t p) :=
  (maximalIdeal A).map (algebraMap A (CompletedTower A t p))

/-- 塔に拡大した極大イデアルを完備化へ移すと、直接の拡大と一致する。 -/
theorem towerMaxIdeal_map_completed :
    (towerMaxIdeal A t p).map (algebraMap (Tower A t p) (CompletedTower A t p)) =
      completedTowerMaxIdeal A t p := by
  simp only [towerMaxIdeal, completedTowerMaxIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- 完備化上の正規化長さ：非完備な塔に制限して測る。 -/
noncomputable def completedTowerLength :
    NormalizedLength (CompletedTower A t p) (completedTowerMaxIdeal A t p) :=
  (towerLength A t p).comap (algebraMap (Tower A t p) (CompletedTower A t p)) _
    (towerMaxIdeal_map_completed A t p).le

variable (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (C : Type u) [CommRing C] [Algebra A C] [Algebra D C]
    [Algebra (Tower A t p) C] [Algebra (CompletedTower A t p) C]
    [IsScalarTower A D C] [IsScalarTower A (Tower A t p) C]
    [IsScalarTower A (CompletedTower A t p) C]
    [IsScalarTower (Tower A t p) (CompletedTower A t p) C]

omit [IsScalarTower A (CompletedTower A t p) C] in
/-- 完備化を経由して係数を制限しても、長さ代数の長さは変わらない。 -/
theorem towerLengthOn_eq_completedTowerLength
    (M : Type u) [AddCommGroup M] [Module C M] :
    (towerLengthOn A D hinj t p C).len M =
      (letI := Module.compHom M (algebraMap (CompletedTower A t p) C)
       (completedTowerLength A t p).len M) := by
  exact (towerLength A t p).len_congr
    ((ModuleCat.restrictScalars (algebraMap (Tower A t p) C)).obj (ModuleCat.of C M))
    ((ModuleCat.restrictScalars (algebraMap (Tower A t p) (CompletedTower A t p))).obj
      ((ModuleCat.restrictScalars (algebraMap (CompletedTower A t p) C)).obj (ModuleCat.of C M)))
    (ModuleCat.restrictScalarsComp'App
      (algebraMap (Tower A t p) (CompletedTower A t p))
      (algebraMap (CompletedTower A t p) C) (algebraMap (Tower A t p) C)
      (IsScalarTower.algebraMap_eq _ _ _) (ModuleCat.of C M)).toLinearEquiv

include hinj in
omit [Algebra (Tower A t p) C] [IsScalarTower A (Tower A t p) C]
  [IsScalarTower (Tower A t p) (CompletedTower A t p) C] in
/-- `m_A` の完備化・`C` での像は `m_D C` に含まれる。 -/
theorem completedTowerMaxIdeal_map_le :
    (completedTowerMaxIdeal A t p).map (algebraMap (CompletedTower A t p) C) ≤
      (maximalIdeal D).map (algebraMap D C) := by
  dsimp only [completedTowerMaxIdeal]
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A D C,
    ← Ideal.map_map]
  exact Ideal.map_mono (maximalIdeal_map_le_of_finite_of_injective A D hinj)

include hinj in
omit [Algebra (Tower A t p) C] [IsScalarTower A (Tower A t p) C]
  [IsScalarTower (Tower A t p) (CompletedTower A t p) C] in
/-- パラメータ系の Koszul ホモロジーは、完備化した塔の `m_A` の冪で消える。
任意の係数拡大に共通する消去冪と `m_A D ⊆ m_D` から従う。 -/
theorem isPowTorsion_completedTower_koszul [IsNoetherianRing D]
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℕ) :
    letI := Module.compHom (koszulHomologySelf (fun j ↦ algebraMap D C (z j)) i)
      (algebraMap (CompletedTower A t p) C)
    IsPowTorsion (completedTowerMaxIdeal A t p)
      (koszulHomologySelf (fun j ↦ algebraMap D C (z j)) i) := by
  apply IsPowTorsion.comap _ (completedTowerMaxIdeal_map_le A t p D hinj C)
  obtain ⟨N, hN⟩ := exists_pow_annihilates_koszul_baseChange D z hz
  refine ⟨N, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator]
  intro a ha
  have hann := hN C (algebraMap D C) (-(i : ℤ))
  rw [Ideal.map_pow] at hann
  exact hann ha

end SerrePositivity.Section2
