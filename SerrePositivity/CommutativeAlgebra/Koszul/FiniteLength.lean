module

public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.PerfectComplex.Free.K0

/-! # パラメータ系の Koszul ホモロジーの有限長性

## 概要

Noether 局所環のパラメータ系 `z` について、Koszul ホモロジーは全次数で有限長である
（`isFiniteLength_koszulHomology_of_isSystemOfParameters`）。さらに、極大イデアルのある冪が、任意の係数拡大
`B ⊗ K(z)` のホモロジーを全次数で消す（`exists_pow_annihilates_koszul_baseChange`）。

## 方針

Koszul ホモロジーは `(z)` で消え、`(z)` は `m` 準素なので有限長。冪の消去は、`z_i` 倍が Koszul 複体上で
零ホモトピックであることから、拡大先に依らない冪を取る。

## 規約

Koszul 複体は `Koszul/Basic.lean`。

## 使われ方

Koszul 重複度の公式（`KoszulMultiplicity/Formula`）、Frobenius 冪の Koszul 極限、根の塔の Koszul、
論文 §2 の完全環の Koszul 長さ、CLMST の源の Euler 評価。
-/

public section

universe u

namespace SerrePositivity

open IsLocalRing
open CategoryTheory

/-- Noether 局所環のパラメータ系の Koszul ホモロジーは、全次数で有限長である。 -/
theorem isFiniteLength_koszulHomology_of_isSystemOfParameters
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℤ) :
    IsFiniteLength D ((koszulComplex z).homology i) := by
  let : IsArtinianRing (D ⧸ maximalIdeal D) :=
    inferInstanceAs (IsArtinianRing (ResidueField D))
  let : IsArtinianRing (D ⧸ Ideal.span (Set.range z)) :=
    isArtinianRing_quotient_of_le_radical (maximalIdeal D) _ (by rw [hz.2])
  exact homology_finiteLength_of_isPerfectSupported (isPerfectSupported_koszulComplex z) i

set_option backward.isDefEq.respectTransparency false in
/-- パラメータ系の Koszul ホモロジーは、任意の係数拡大・任意の次数で共通の冪に消される。
この冪は元の環とパラメータ系だけで選び、拡大先の Noether 性・平坦性は不要である。 -/
theorem exists_pow_annihilates_koszul_baseChange
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    ∃ N : ℕ, ∀ (C : Type u) [CommRing C] (φ : D →+* C) (i : ℤ),
      ((maximalIdeal D) ^ N).map φ ≤
        Module.annihilator C ((koszulComplex (φ ∘ z)).homology i) := by
  obtain ⟨v, hv⟩ := isSupported_koszulComplex z
  let I := Ideal.span (Set.range fun j ↦ z j ^ v)
  have hI : maximalIdeal D ≤ I.radical := by
    rw [← hz.2]
    apply Ideal.radical_le_radical_iff.mpr
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_radical_iff.mpr ⟨v, Ideal.subset_span (Set.mem_range_self j)⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hI
    (IsNoetherian.noetherian _)
  refine ⟨N, fun C _ φ i ↦ (Ideal.map_mono hN).trans ?_⟩
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  change φ (z j ^ v) ∈ Module.annihilator C ((koszulComplex (φ ∘ z)).homology i)
  obtain ⟨H⟩ := hv j
  have H' := (ModuleCat.extendScalars.{u, u, u} φ).mapHomotopy H
  rw [extendScalars_mapHomologicalComplex_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at H'
  have hh := H'.homologyMap_eq i
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at hh
  let e := ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (baseChangeKoszulIso φ z)).toLinearEquiv
  rw [Module.mem_annihilator]
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← e.map_smul]
  have hx : φ (z j ^ v) • x = 0 :=
    congrArg (fun f ↦ (f : (baseChange φ (koszulComplex z)).homology i ⟶ _).hom x) hh
  rw [hx, map_zero]

end SerrePositivity
