module

public import SerrePositivity.CLMST.CompletedTargetLength
public import SerrePositivity.CLMST.NonunitIsogeny
public import SerrePositivity.CLMST.StagePowerMembership

/-! # 零化冪とパラメータ選択から実際の Euler 比較へ

非単元のエタール開集合の元・正の零化指数を選び、生成イデアルを保つ列変更と
最後の正の冪の選択を行う。長さの有限性・余核の零化・最後の元の所属を
未知の仮定として要求せず、既存の具体的比較へ渡す。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory
attribute [local instance] HasDerivedCategory.standard

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 任意の有限段のパラメータ系に対し、実際の零化冪と所属を満たす列を選び Euler 比較を適用する。 -/
theorem exists_selected_parameter_euler_comparison
    (n : ℕ) {r : ℕ} (hr : h = r + 1) (y : Fin (r + 1) → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (StageAlgebra A D t p n) y) :
    let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    ∃ (y' : Fin (r + 1) → StageAlgebra A D t p n) (k : ℕ),
      Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
      IsSystemOfParameters (StageAlgebra A D t p n)
        (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
      (let lam := completedTensorLength A D t p
         (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
       let z := (stageToCompletedTensor A D t p n).toRingHom ∘
         Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)
       let S := (CompletedTower A t p) ⊗[A] D
       let C := RPerfd A D t p hperf
       (lambdaEuler lam ((koszulModuleFunctor z).obj
         (ModuleCat.of S (AlgebraMapCokernel S C))) = 0) ∧
       (lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S C)) =
         lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S S))) ∧
       (∀ q : ℤ, lam.len (((koszulModuleFunctor z).obj
         (ModuleCat.of S C)).homology q) ≠ ⊤)) := by
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  let : IsLocalRing (StageAlgebra A D t p n) :=
    stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  dsimp only
  have hp : (p : A) ∈ maximalIdeal A := by
    rw [← htp, ← ht]
    exact Ideal.subset_span (Set.mem_range_self _)
  obtain ⟨g, N, hg, _, hgmD, hNpos, hEtale, _, hN⟩ :=
    exists_nonunit_completedTensor_positive_isogeny A D t p hperf hinj hp
  have htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D := by
    intro i
    rw [← hsop.2]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
  have hgD : algebraMap A D g ≠ 0 := fun hzero ↦ hg (hinj (hzero.trans (map_zero _).symm))
  have hgreg : IsSMulRegular D (algebraMap A D g) := fun x y hxy ↦
    mul_left_cancel₀ hgD hxy
  obtain ⟨y', k, hspan, hk, hparam, hmem⟩ :=
    stage_parameter_power_selection_completed_of_regular_base A D t p htD n
      g hgmD hgreg N hNpos y hy
  let w := Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)
  have hprefix : Fin.init ((stageToCompletedTensor A D t p n).toRingHom ∘ w) =
      stageToCompletedTensor A D t p n ∘ Fin.init y' := by
    funext i
    simp only [Fin.init, Function.comp_apply, w, Fin.snoc_castSucc]
    rfl
  have hscalar : algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D)
      (algebraMap A (CompletedTower A t p) g) =
      algebraMap A ((CompletedTower A t p) ⊗[A] D) g :=
    (IsScalarTower.algebraMap_apply A (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) g).symm
  have hLast : stageToCompletedTensor A D t p n (w (Fin.last r)) ∈
      Ideal.span (Set.range (Fin.init ((stageToCompletedTensor A D t p n).toRingHom ∘ w))) ⊔
        Ideal.span {(algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D)
          (algebraMap A (CompletedTower A t p) g)) ^ N} := by
    rw [hprefix, hscalar]
    exact hmem
  have hcompare := completedTensor_stage_parameter_euler_comparison A D hinj hres
    t hdimA hdimD hpos ht hsop p htp e he hperf g hg hEtale n hr w hparam
    (algebraMap A (CompletedTower A t p) g) N hN hLast
  refine ⟨y', k, hspan, hk, hparam, ?_⟩
  refine ⟨hcompare.1, hcompare.2, ?_⟩
  let : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D
  let R := CompletedTower A t p
  let S := R ⊗[A] D
  let z := (stageToCompletedTensor A D t p n).toRingHom ∘ w
  let lam := completedTensorLength A D t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
  have hJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
    (by
      rw [IsScalarTower.algebraMap_eq A D (StageAlgebra A D t p n)]
      exact (stageAlgebra_algebraMap_injective A D t p n).comp hinj) w hparam
  have hinjC := toMixedPerfectoid_injective_of_domain A D t p hperf hinj g hg hEtale
  have hC : ∀ q : ℤ, q < 0 → lam.len
      (((koszulModuleFunctor z).obj (ModuleCat.of S (RPerfd A D t p hperf))).homology q) ≠ ⊤ := by
    intro q hq
    have hyh : IsSystemOfParameters (StageAlgebra A D t p n)
        (fun j : Fin h ↦ w (Fin.cast hr j)) := by
      subst h
      simpa using hparam
    have hzero := completedTensor_stage_target_koszul_length_eq_zero A D hinj hres
      t hdimA hdimD hpos ht hsop p htp e he hperf g hg hEtale n
      (fun j : Fin h ↦ w (Fin.cast hr j)) hyh q hq
    subst h
    change lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (RPerfd A D t p hperf))).homology q) = 0 at hzero
    rw [hzero]
    exact ENNReal.zero_ne_top
  have lNegative := completedTensor_stage_cokernel_negative_length_ne_top A D t p _ hperf
    hp hinjC n w hJ hC
  exact lambdaKoszul_algebraMap_target_ne_top_of_last_mem_span_sup lam
    (RPerfd A D t p hperf) hinjC (completedTensorMaxIdeal_fg A D t p) z hJ
    ((algebraMap R S (algebraMap A R g)) ^ N)
    (perfectoidizationCokernel_annihilated R S p hperf (algebraMap A R g) N hN) hLast
    (completedTensor_stage_koszul_length_ne_top A D t p _ hp n w hJ) lNegative

end SerrePositivity.CLMST
