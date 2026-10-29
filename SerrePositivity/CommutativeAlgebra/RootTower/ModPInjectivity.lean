module

public import SerrePositivity.CommutativeAlgebra.RootTower.ModPFrobenius
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.RingTheory.Ideal.GoingUp

/-! # 有限段Frobenius商射の単射性

根を零にした商が整域なら、mod p 商からの整拡大と Frobenius の単射性により
商射の核は零となる。最小パラメータ系の場合は、その整域性も証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.Section2
open IsLocalRing
variable (A : Type*) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- pは、そのp冪根が生成するイデアルの逆像に入る。 -/
theorem span_p_le_comap_stageRoot (n : ℕ) (j : Fin h) (htj : t j = (p : A)) :
    Ideal.span {(p : A)} ≤
      (Ideal.span {stageX A t p n j}).comap (algebraMap A (TowerStage A t p n)) := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← htj, ← mk_X_pow A t p n j]
  exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _
    (pow_pos (Fact.out : p.Prime).pos n)

/-- 商環が整域なら、有限段からのFrobenius商射は単射。
冪級数表示や全射性には依存しない。 -/
theorem stageRootModPFrobenius_injective_of_isDomain
    [CharP (A ⧸ Ideal.span {(p : A)}) p]
    [IsDomain (A ⧸ Ideal.span {(p : A)})]
    (n : ℕ) (j : Fin h) (htj : t j = (p : A))
    [IsDomain (TowerStage A t p n ⧸ Ideal.span {stageX A t p n j})] :
    Function.Injective (stageRootModPFrobenius A t p n j htj) := by
  let Q := A ⧸ Ideal.span {(p : A)}
  let B := TowerStage A t p n ⧸ Ideal.span {stageX A t p n j}
  let : Algebra Q B := Ideal.Quotient.algebraQuotientOfLEComap
    (span_p_le_comap_stageRoot A t p n j htj)
  let : IsScalarTower A Q B := IsScalarTower.of_algebraMap_eq' rfl
  let := isIntegral_towerStage A t p n
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_surjective
    (Ideal.Quotient.mkₐ A _) Ideal.Quotient.mk_surjective
  let : Algebra.IsIntegral Q B := ⟨fun b ↦ (Algebra.IsIntegral.isIntegral (R := A) b).tower_top⟩
  let f := stageRootModPFrobenius A t p n j htj
  have hcomp : f.comp (algebraMap Q B) = iterateFrobenius Q p n := by
    ext a
    exact stageModPFrobenius_algebraMap A t p n a
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply Ideal.eq_bot_of_under_eq_bot (R := Q)
  change Ideal.comap (algebraMap Q B) (RingHom.ker f) = ⊥
  rw [RingHom.comap_ker, hcomp]
  exact (RingHom.injective_iff_ker_eq_bot (iterateFrobenius Q p n)).mp
    (iterateFrobenius_inj Q p n)

/-- 最小パラメータ系の先頭の根を零にした有限段の商は整域。 -/
theorem stageRootQuotient_isDomain_of_parameters [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 1) → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdim : ringKrullDim A = r + 1) (n : ℕ) :
    IsDomain (TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0}) := by
  have htmem : ∀ i, t i ∈ maximalIdeal A := fun i ↦
    ht ▸ Ideal.subset_span (Set.mem_range_self i)
  let := isLocalRing_towerStage A t p htmem n
  let := towerStage_finite A t p n
  let := towerStage_free A t p n
  let := isIntegral_towerStage A t p n
  let : IsNoetherianRing (TowerStage A t p n) := IsNoetherianRing.of_finite A _
  have hdimn : ringKrullDim (TowerStage A t p n) = r + 1 :=
    (ringKrullDim_eq_of_integral_of_injective A _
      (FaithfulSMul.algebraMap_injective A _)).trans hdim
  have hgen := span_stageX_eq_maximalIdeal A t p htmem ht n
  let : IsRegularLocalRing (TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0}) :=
    (isRegularLocalRing_quotient_head_and_dim
      (stageX A t p n) hgen hdimn).1
  obtain ⟨rs, hreg, hspan, _⟩ := exists_regular_generators
    (TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0})
  exact isDomain_of_regular_generators rs hreg hspan

end SerrePositivity.Section2
