module

public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import SerrePositivity.PerfectComplex.OrdinaryEuler
public import SerrePositivity.PerfectComplex.Closure

/-! # パラメータ系の Koszul ホモロジーの有限長性

パラメータイデアルの商は Artin 環であり、Koszul 複体はそのイデアルに台を持つ。
したがって各次数のホモロジーは有限長である。Frobenius 冪の列にも適用できる。
さらに、元の Koszul 複体の零ホモトピーから、任意の係数拡大・全次数に共通する
極大イデアルの消去冪を選ぶ。
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
