module
public import SerrePositivity.KST.SConstruction.SerreIntervalDiagonalEndpoints
public import SerrePositivity.DifferentialGraded.Complexes.Currying
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex

/-! # 元の鎖区間の Serre 対角の余結合律
概要：元の鎖区間の二重対角の二つの括り方を、同じ tensor 結合射で比較する。
方針：零頂点と辺で判定し、辺では同じ三つの純 tensor 項を回収する。
規約：辺の向きと元の tensor 因子順を保つ。使われ方：dg nerve tensor 比較の結合則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
private lemma diagonal_coassoc_edge {A : Type u} [CommRing A] {P : Complex A}
    (d : P ⟶ P ⊗ P) (z₀ z₁ : P.X 0) (e : P.X (-1))
    (h₀ : d.f 0 z₀ = ιTensorObj P P 0 0 0 rfl (z₀ ⊗ₜ[A] z₀))
    (h₁ : d.f 0 z₁ = ιTensorObj P P 0 0 0 rfl (z₁ ⊗ₜ[A] z₁))
    (he : d.f (-1) e = ιTensorObj P P 0 (-1) (-1) (by omega) (z₀ ⊗ₜ[A] e) +
      ιTensorObj P P (-1) 0 (-1) (by omega) (e ⊗ₜ[A] z₁)) :
    (α_ P P P).hom.f (-1) ((d ⊗ₘ 𝟙 P).f (-1) (d.f (-1) e)) =
      (𝟙 P ⊗ₘ d).f (-1) (d.f (-1) e) := by
  simp only [he, map_add]
  rw [tensorMap_apply, tensorMap_apply, tensorMap_apply, tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, h₀, h₁, he,
    TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
  have hA := associator_apply_of_sums P P P 0 0 (-1) 0 (-1) (-1)
    (by omega) (by omega) (by omega) z₀ z₀ e
  have hB := associator_apply_of_sums P P P 0 (-1) 0 (-1) (-1) (-1)
    (by omega) (by omega) (by omega) z₀ e z₁
  have hC := associator_apply_of_sums P P P (-1) 0 0 (-1) 0 (-1)
    (by omega) (by omega) (by omega) e z₁ z₁
  simpa only [add_assoc] using
    congrArg₂ (· + ·) hA (congrArg₂ (· + ·) hB hC)

variable (A : Type u) [CommRing A]

/-- Serre 対角は、元の tensor 結合射に沿って余結合的。 -/
lemma serreIntervalDiagonal_coassoc :
    serreIntervalDiagonal A ≫
        (serreIntervalDiagonal A ⊗ₘ 𝟙 (serreInterval A)) ≫
        (α_ (serreInterval A) (serreInterval A) (serreInterval A)).hom =
      serreIntervalDiagonal A ≫ (𝟙 (serreInterval A) ⊗ₘ serreIntervalDiagonal A) := by
  apply serreInterval_hom_ext A
  · apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (α_ (serreInterval A) (serreInterval A) (serreInterval A)).hom.f 0
        ((serreIntervalDiagonal A ⊗ₘ 𝟙 (serreInterval A)).f 0
          ((serreIntervalDiagonal A).f 0 (cycleFromUnit _ (serreIntervalZero A)).val)) =
      (𝟙 (serreInterval A) ⊗ₘ serreIntervalDiagonal A).f 0
        ((serreIntervalDiagonal A).f 0 (cycleFromUnit _ (serreIntervalZero A)).val)
    simp only [serreIntervalDiagonal_zero_value]
    rw [tensorMap_apply, tensorMap_apply]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalDiagonal_zero_value]
    exact associator_apply _ _ _ 0 0 0 0 rfl _ _ _
  · exact diagonal_coassoc_edge (serreIntervalDiagonal A)
      (cycleFromUnit _ (serreIntervalZero A)).val
      (cycleFromUnit _ (serreIntervalOne A)).val (serreIntervalEdge A)
      (serreIntervalDiagonal_zero_value A) (serreIntervalDiagonal_one_value A)
      (serreIntervalDiagonal_edge A)

end SerrePositivity.KST.SConstruction
