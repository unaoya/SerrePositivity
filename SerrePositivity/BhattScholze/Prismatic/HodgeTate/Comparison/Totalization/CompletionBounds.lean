module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Koszul 簡約の下界と実際の完備化の下界

## 概要
一つのスカラー錐のホモロジーの下界は、同じスカラーの全ての冪と完備化へ渡る。

## 方針
長完全列でスカラー作用の全射・単射を取り出し、その反復を用いる。
holim では直積のホモロジーと既存の差分の長完全列を使う。

## 規約
複体の上方有界性・スカラーの正則性・通常の商による計算は仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の一様な下界の、主元ごとの鎖複体上の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DerivedCompletion SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

private theorem exact_comp_zero {S : ShortComplex (ModuleCat.{u} R)} (_h : S.Exact) :
    S.f ≫ S.g = 0 := S.zero

/-- スカラー作用の全射性と次の次数での単射性は、その錐のホモロジーを消す。 -/
theorem scalarCone_isZero_of_surjective_of_injective (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (hs : Function.Surjective (fun x : K.homology i => a • x))
    (hi : Function.Injective (fun x : K.homology (i+1) => a • x)) :
    IsZero (((scalarConeFunctor a).obj K).homology i) := by
  haveI : Epi (homologyMap (smulId a K) i) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    simpa only [smulId, homologyMap_smul, homologyMap_id, ModuleCat.hom_smul,
      ModuleCat.hom_id, LinearMap.coe_smul, LinearMap.id_coe, Pi.smul_def, id_eq] using hs
  haveI : Mono (homologyMap (smulId a K) (i+1)) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    simpa only [smulId, homologyMap_smul, homologyMap_id, ModuleCat.hom_smul,
      ModuleCat.hom_id, LinearMap.coe_smul, LinearMap.id_coe, Pi.smul_def, id_eq] using hi
  apply (Cone.exact₃ (smulId a K) i (i+1) rfl).isZero_X₂
  · apply (cancel_epi (homologyMap (smulId a K) i)).mp
    simpa only [comp_zero] using exact_comp_zero (Cone.exact₂ (smulId a K) i)
  · apply (cancel_mono (homologyMap (smulId a K) (i+1))).mp
    simpa only [zero_comp] using exact_comp_zero (Cone.exact₁ (smulId a K) i (i+1) rfl)

/-- 一つのスカラー錐の下界は、正則性を要求せず全ての冪に対して一様である。 -/
theorem scalarPowerCone_lowerBound (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (h : ∀ i : ℤ, i < b → IsZero (((scalarConeFunctor a).obj K).homology i))
    (n : ℕ) (i : ℤ) (hi : i < b) :
    IsZero (((scalarConeFunctor (a ^ n)).obj K).homology i) := by
  have hs := cochain_homology_smul_surjective_of_scalarCone_isZero a K i (h i hi)
  have hj : IsZero (((scalarConeFunctor a).obj K).homology ((i+1)-1)) := by
    simpa using h i hi
  have ht := cochain_homology_smul_injective_of_scalarCone_isZero a K (i+1) hj
  apply scalarCone_isZero_of_surjective_of_injective (a ^ n) K i
  · simpa only [smul_iterate] using hs.iterate n
  · simpa only [smul_iterate] using ht.iterate n

/-- 逆系の各段の隣接する二次数が零なら、実際のholimのその次数も零である。 -/
theorem tower_homology_isZero
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n+1) ⟶ K n) (i : ℤ)
    (hi : ∀ n, IsZero ((K n).homology i))
    (hprev : ∀ n, IsZero ((K n).homology (i-1))) :
    IsZero ((complexTowerHomotopyLimit R K t).homology i) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : complexTowerHomologyBoundary R K t i x = 0 := by
    funext n
    exact (ModuleCat.isZero_iff_subsingleton.mp (hi n)).elim _ _
  obtain ⟨y, hy⟩ := (complexTowerHomologyBoundary_zero_iff R K t i x).mp hx
  have hyzero : y = 0 := by
    funext n
    exact (ModuleCat.isZero_iff_subsingleton.mp (hprev n)).elim _ _
  simpa only [hyzero, map_zero] using hy.symm

/-- 各冪のKoszul段の一様な下界は、既存の完備化関手の値へ渡る。 -/
theorem completion_lowerBound_of_powerBounds (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (h : ∀ n : ℕ, ∀ i : ℤ, i < b →
      IsZero ((complexPowerKoszulStage R a K n).homology i))
    (i : ℤ) (hi : i < b) :
    IsZero (((complexCompletionFunctor R a).obj K).homology i) :=
  tower_homology_isZero (complexPowerKoszulStage R a K)
    (complexPowerKoszulTransition R a K) i (fun n => h n i hi)
    (fun n => h n (i-1) (by omega))

/-- 最初のKoszul簡約の下界から、実際の主元完備化の同じ下界が従う。 -/
theorem completion_lowerBound_of_scalarCone (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (h : ∀ i : ℤ, i < b → IsZero (((scalarConeFunctor a).obj K).homology i))
    (i : ℤ) (hi : i < b) :
    IsZero (((complexCompletionFunctor R a).obj K).homology i) :=
  completion_lowerBound_of_powerBounds a K b
    (fun n j hj => scalarPowerCone_lowerBound a K b h n j hj) i hi

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
