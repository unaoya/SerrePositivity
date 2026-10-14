module

public import SerrePositivity.CommutativeAlgebra.RootTower.ModPSurjectivity
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedRoots
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedRepresentatives
public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality
public import SerrePositivity.CommutativeAlgebra.PowerSeriesCoefficientQuotient

/-! # 標準的な根の塔の完備化のmod p Frobenius

有限段のFrobenius評価の全射性を、完備塔のmod p上のp乗根へ移す。
perfectoid性やperfectoid化の存在引用を仮定せず、有限段の代表と根の座標を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.Section2
open MvPolynomial
variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- 有限段のFrobenius評価は、任意のA代数への写像のmod pにおける冪と両立する。 -/
theorem stageModPFrobenius_map_eq_pow
    (S : Type u) [CommRing S] [Algebra A S] (n : ℕ)
    (f : TowerStage A t p n →ₐ[A] S) (z : TowerStage A t p n) :
    modPMap p (algebraMap A S) (stageModPFrobenius A t p n z) =
      (Ideal.Quotient.mk (Ideal.span {(p : S)}) (f z)) ^ (p ^ n) := by
  classical
  by_cases hsub : Subsingleton (ModP S p)
  · exact hsub.elim _ _
  let : Nontrivial (ModP S p) := not_subsingleton_iff_nontrivial.mp hsub
  let : CharP (ModP S p) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : S)}))]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))
  let q := Ideal.Quotient.mk (Ideal.span {(p : S)})
  have heq : (modPMap p (algebraMap A S)).comp (stageModPFrobenius A t p n) =
      (iterateFrobenius (ModP S p) p n).comp (q.comp f.toRingHom) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change modPMap p (algebraMap A S)
          (stageModPFrobenius A t p n (algebraMap A _ a)) =
        q (f (algebraMap A _ a)) ^ (p ^ n)
      rw [stageModPFrobenius_algebraMap, map_pow, f.commutes]
      rfl
    · intro i
      change modPMap p (algebraMap A S)
          (stageModPFrobenius A t p n (stageX A t p n i)) =
        q (f (stageX A t p n i)) ^ (p ^ n)
      rw [stageModPFrobenius_stageX]
      change q (algebraMap A S (t i)) = q (f (stageX A t p n i)) ^ (p ^ n)
      rw [← map_pow, ← map_pow]
      change q (algebraMap A S (t i)) = q (f
        (Ideal.Quotient.mk (towerRel A t p n) (X i) ^ (p ^ n)))
      rw [mk_X_pow, f.commutes]
  exact DFunLike.congr_fun heq z

/-- 一段のFrobenius評価が全射なら、完備塔のmod pの全ての元がp乗になる。 -/
theorem completedTower_modP_pow_surjective_of_stageFrobenius_surjective
    (hstage : Function.Surjective (stageModPFrobenius A t p 1)) :
    Function.Surjective (fun x : ModP (CompletedTower A t p) p ↦ x ^ p) := by
  classical
  let C := CompletedTower A t p
  let Q := ModP C p
  let q : C →+* Q := Ideal.Quotient.mk (Ideal.span {(p : C)})
  by_cases hsub : Subsingleton Q
  · let := hsub
    exact fun x ↦ ⟨0, Subsingleton.elim _ _⟩
  let : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hsub
  let : CharP Q p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))
  let F := frobenius Q p
  have hcoeff (a : A) : q (algebraMap A C a) ∈ F.range := by
    obtain ⟨z, hz⟩ := hstage (Ideal.Quotient.mk (Ideal.span {(p : A)}) a)
    refine ⟨q (algebraMap (TowerStage A t p 1) C z), ?_⟩
    have hh := stageModPFrobenius_map_eq_pow A t p C 1
      (IsScalarTower.toAlgHom A (TowerStage A t p 1) C) z
    rw [hz] at hh
    simpa only [pow_one, IsScalarTower.toAlgHom_apply, modPMap,
      Ideal.quotientMap_mk, F, q, frobenius_def] using hh.symm
  have hroot (n : ℕ) (i : Fin h) : q (completedTowerRoot A t p n i) ∈ F.range := by
    refine ⟨q (completedTowerRoot A t p (n + 1) i), ?_⟩
    change q (completedTowerRoot A t p (n + 1) i) ^ p = _
    rw [← map_pow, completedTowerRoot_succ_pow]
  have hfinite (n : ℕ) (z : TowerStage A t p n) :
      q (algebraMap (TowerStage A t p n) C z) ∈ F.range := by
    obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction φ using MvPolynomial.induction_on with
    | C a =>
      change q (algebraMap (TowerStage A t p n) C (algebraMap A _ a)) ∈ F.range
      rw [← IsScalarTower.algebraMap_apply A (TowerStage A t p n) C]
      exact hcoeff a
    | add φ ψ hφ hψ =>
      simp only [map_add]
      exact F.range.add_mem hφ hψ
    | mul_X φ i hφ =>
      simp only [map_mul]
      exact F.range.mul_mem hφ (hroot n i)
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, _, z, hz⟩ := exists_completedTower_stage_representative A t p a 1 0
  have heq : q (algebraMap (TowerStage A t p n) C z) = q a := by
    apply Ideal.Quotient.eq.mpr
    simpa only [pow_one] using hz
  obtain ⟨y, hy⟩ := hfinite n z
  exact ⟨y, hy.trans heq⟩

/-- mod pの標準冪級数表示から、完備塔のmod p Frobeniusの全射性を得る。 -/
theorem completedTower_modP_pow_surjective_of_powerSeries
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k)
    (ι : σ → Fin h)
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i) :
    Function.Surjective (fun x : ModP (CompletedTower A t p) p ↦ x ^ p) :=
  completedTower_modP_pow_surjective_of_stageFrobenius_surjective A t p
    (stageModPFrobenius_surjective_of_powerSeries t p e ι he 1)

omit [CharP (A ⧸ Ideal.span {(p : A)}) p] in
/-- Witt係数の標準表示から完備塔のmod p Frobenius全射性を証明する。
正則局所性・次元・座標による極大イデアル生成はこの条件には不要。 -/
theorem completedTower_modP_pow_surjective_of_wittPowerSeries
    (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
    {σ : Type u} [Finite σ]
    (e : A ≃+* MvPowerSeries σ (WittVector p k)) (ι : σ → Fin h)
    (he : ∀ i, e (t (ι i)) = MvPowerSeries.X i) :
    Function.Surjective (fun x : ModP (CompletedTower A t p) p ↦ x ^ p) := by
  let eP := wittPresentedModPEquiv A σ k p e
  let f : k →+* A ⧸ Ideal.span {(p : A)} := eP.symm.toRingHom.comp MvPowerSeries.C
  let : CharP (A ⧸ Ideal.span {(p : A)}) p :=
    charP_of_injective_ringHom (f := f) (eP.symm.injective.comp MvPowerSeries.C_injective) p
  exact completedTower_modP_pow_surjective_of_powerSeries A t p eP ι
    (fun i ↦ wittPresentedModPEquiv_coordinate A σ k p e (t (ι i)) i (he i))

end SerrePositivity.Section2
