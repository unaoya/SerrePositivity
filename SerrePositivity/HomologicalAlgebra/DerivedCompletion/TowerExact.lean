module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerMap
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # 複体塔の短完全列のホモトピー逆極限

holimの二成分表示を使い、各次数の短完全性を直接証明する。
通常の逆極限の完全性やlim¹消滅を仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable (R : Type u) [CommRing R]
variable {K L M : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (u : ∀ n, M (n + 1) ⟶ M n)
    (f : ∀ n, K n ⟶ L n) (g : ∀ n, L n ⟶ M n)
    (hf : ∀ n, t n ≫ f n = f (n + 1) ≫ s n)
    (hg : ∀ n, s n ≫ g n = g (n + 1) ≫ u n)
    (hfg : ∀ n, f n ≫ g n = 0)

include hfg in
/-- 各段の零合成は、holimの実際の写像の零合成を与える。 -/
theorem complexTowerHomotopyLimitMap_comp_zero :
    complexTowerHomotopyLimitMap R t s f hf ≫
      complexTowerHomotopyLimitMap R s u g hg = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega)).injective
  apply Prod.ext
  · funext k
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
      Prod.fst_zero, Pi.zero_apply]
    rw [complexTowerHomotopyLimitDegreeEquiv_map_fst,
      complexTowerHomotopyLimitDegreeEquiv_map_fst]
    exact congrArg (fun q ↦ (q.f i).hom
      ((complexTowerHomotopyLimitDegreeEquiv R K t (i - 1) i (by omega) x).1 k)) (hfg k)
  · funext k
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
      Prod.snd_zero, Pi.zero_apply]
    rw [complexTowerHomotopyLimitDegreeEquiv_map_snd,
      complexTowerHomotopyLimitDegreeEquiv_map_snd]
    exact congrArg (fun q ↦ (q.f (i - 1)).hom
      ((complexTowerHomotopyLimitDegreeEquiv R K t (i - 1) i (by omega) x).2 k)) (hfg k)

/-- 塔の短複体のholimを、実際の複体の短複体として構成する。 -/
def complexTowerHomotopyLimitShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (complexTowerHomotopyLimitMap R t s f hf)
    (complexTowerHomotopyLimitMap R s u g hg)
    (complexTowerHomotopyLimitMap_comp_zero R t s u f g hf hg hfg)

/-- 各段が短完全なら、差分の錐とシフトによるholimの短複体も短完全。 -/
theorem complexTowerHomotopyLimitShortComplex_shortExact
    (hS : ∀ k, (ShortComplex.mk (f k) (g k) (hfg k)).ShortExact) :
    (complexTowerHomotopyLimitShortComplex R t s u f g hf hg hfg).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  change (ShortComplex.mk
    ((complexTowerHomotopyLimitMap R t s f hf).f i)
    ((complexTowerHomotopyLimitMap R s u g hg).f i)
    (congrArg (fun q ↦ q.f i)
      (complexTowerHomotopyLimitMap_comp_zero R t s u f g hf hg hfg))).ShortExact
  have hs (k : ℕ) (j : ℤ) :
      ((ShortComplex.mk (f k) (g k) (hfg k)).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) j)).ShortExact :=
    (hS k).map_of_exact (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) j)
  have hfinj (k : ℕ) (j : ℤ) : Function.Injective ((f k).f j) :=
    (ModuleCat.mono_iff_injective _).mp (hs k j).mono_f
  have hgsurj (k : ℕ) (j : ℤ) : Function.Surjective ((g k).f j) :=
    (ModuleCat.epi_iff_surjective _).mp (hs k j).epi_g
  have hexact (k : ℕ) (j : ℤ) (y : (L k).X j) (hy : (g k).f j y = 0) :
      ∃ x, (f k).f j x = y :=
    (ShortComplex.moduleCat_exact_iff _).mp (hs k j).exact y hy
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    let v := complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega) y
    have hv₁ (k : ℕ) : (g k).f i (v.1 k) = 0 := by
      have h := congrArg (fun z ↦
        (complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega) z).1 k) hy
      simpa only [complexTowerHomotopyLimitDegreeEquiv_map_fst, map_zero,
        Prod.fst_zero, Pi.zero_apply] using h
    have hv₂ (k : ℕ) : (g k).f (i - 1) (v.2 k) = 0 := by
      have h := congrArg (fun z ↦
        (complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega) z).2 k) hy
      simpa only [complexTowerHomotopyLimitDegreeEquiv_map_snd, map_zero,
        Prod.snd_zero, Pi.zero_apply] using h
    choose x₁ hx₁ using fun k ↦ hexact k i (v.1 k) (hv₁ k)
    choose x₂ hx₂ using fun k ↦ hexact k (i - 1) (v.2 k) (hv₂ k)
    refine ⟨(complexTowerHomotopyLimitDegreeEquiv R K t (i - 1) i (by omega)).symm (x₁, x₂), ?_⟩
    apply (complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega)).injective
    apply Prod.ext
    · funext k
      rw [complexTowerHomotopyLimitDegreeEquiv_map_fst, LinearEquiv.apply_symm_apply]
      exact hx₁ k
    · funext k
      rw [complexTowerHomotopyLimitDegreeEquiv_map_snd, LinearEquiv.apply_symm_apply]
      exact hx₂ k
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    apply (complexTowerHomotopyLimitDegreeEquiv R K t (i - 1) i (by omega)).injective
    apply Prod.ext
    · funext k
      apply hfinj k i
      have h := congrArg (fun z ↦
        (complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega) z).1 k) hxy
      simpa only [complexTowerHomotopyLimitDegreeEquiv_map_fst] using h
    · funext k
      apply hfinj k (i - 1)
      have h := congrArg (fun z ↦
        (complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega) z).2 k) hxy
      simpa only [complexTowerHomotopyLimitDegreeEquiv_map_snd] using h
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro y
    let v := complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega) y
    choose x₁ hx₁ using fun k ↦ hgsurj k i (v.1 k)
    choose x₂ hx₂ using fun k ↦ hgsurj k (i - 1) (v.2 k)
    refine ⟨(complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega)).symm (x₁, x₂), ?_⟩
    apply (complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega)).injective
    apply Prod.ext
    · funext k
      rw [complexTowerHomotopyLimitDegreeEquiv_map_fst, LinearEquiv.apply_symm_apply]
      exact hx₁ k
    · funext k
      rw [complexTowerHomotopyLimitDegreeEquiv_map_snd, LinearEquiv.apply_symm_apply]
      exact hx₂ k

end SerrePositivity.DerivedCompletion
