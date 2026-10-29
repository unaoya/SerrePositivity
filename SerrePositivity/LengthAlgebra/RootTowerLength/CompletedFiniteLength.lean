module

public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedNormalized
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import SerrePositivity.LengthAlgebra.FinitelyGeneratedFiniteLength

/-! # 完備塔上の有限生成な冪ねじれ加群の長さの有限性

pが基底の極大イデアルに属するとき、その冪商を未完備塔の有限表示商へ比較する。
完備塔自身のNoether性を使わず、有限生成な冪ねじれ加群へ有限性を移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)

include hp in
/-- 完備塔の極大イデアルの拡張の冪商は、正規化長さが有限。 -/
theorem completedNormalizedLength_quotient_pow_ne_top (n : ℕ) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ (completedTowerMaxIdeal A t p) ^ n) ≠ ⊤ := by
  let S := Tower A t p
  let I : Ideal S := Ideal.span {(p : S)}
  let H : Ideal S := (towerMaxIdeal A t p) ^ n
  have hI : I.FG := Submodule.fg_span_singleton _
  have hpS : (p : S) ∈ towerMaxIdeal A t p := by
    simpa using Ideal.mem_map_of_mem (algebraMap A S) hp
  have hIH : I ^ n ≤ H := pow_le_pow_left'
    (((towerMaxIdeal A t p).span_singleton_le_iff_mem).mpr hpS) n
  have hH : H.FG := ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A S)).pow
  let : Module.FinitePresentation S (S ⧸ H) :=
    Module.finitePresentation_of_surjective H.mkQ H.mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      exact hH)
  have htH : IsPowTorsion (towerMaxIdeal A t p) (S ⧸ H) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
  have hmap : H.map (algebraMap S (CompletedTower A t p)) =
      (completedTowerMaxIdeal A t p) ^ n := by
    rw [Ideal.map_pow, towerMaxIdeal_map_completed]
  let e : (CompletedTower A t p ⧸ (completedTowerMaxIdeal A t p) ^ n) ≃ₐ[S] S ⧸ H :=
    (Ideal.quotientEquivAlgOfEq S hmap.symm).trans
      (adicCompletionOpenQuotientEquiv I H n hIH hI)
  let Q := CompletedTower A t p ⧸ (completedTowerMaxIdeal A t p) ^ n
  let : Module S Q := Module.compHom Q (algebraMap S (CompletedTower A t p))
  let E : Q ≃ₗ[S] S ⧸ H := { e.toAddEquiv with
    map_smul' := by
      intro r x
      change e (algebraMap S Q r * x) = algebraMap S (S ⧸ H) r * e x
      rw [map_mul, e.commutes] }
  rw [completedNormalizedLength_len]
  change towerLengthFun A t p Q ≠ ⊤
  rw [towerLengthFun_congr E]
  exact towerLengthFun_ne_top_of_finitePresentation A t p ht (S ⧸ H) htH

include hp in
/-- 完備塔上の有限生成な冪ねじれ加群は、正規化長さが有限。
完備塔のNoether性・加群の有限表示性は不要。 -/
theorem completedNormalizedLength_ne_top_of_finite
    (M : Type u) [AddCommGroup M] [Module (CompletedTower A t p) M]
    [Module.Finite (CompletedTower A t p) M]
    (hM : IsPowTorsion (completedTowerMaxIdeal A t p) M) :
    (completedNormalizedLength A t p ht).len M ≠ ⊤ :=
  NormalizedLength.len_ne_top_of_finite_of_powQuotient_ne_top
    (completedNormalizedLength A t p ht)
    (completedNormalizedLength_quotient_pow_ne_top A t p ht hp) hM

end SerrePositivity.RootTowerLength
