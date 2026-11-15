module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealApproximation

/-!
概要：有限アフィン被覆上の生成元の模型から、有限型イデアル層の模型を作る。
方針：K.map f の有限型部分イデアルに有限個の生成元を含め、map/comap の随伴で比較する。
規約：f は affine、基底は qcqs。忠実平坦性は仮定しない。
使われ方：Stacks 0B8W (3) の有限型イデアル層の有限段への降下。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- affine な射の有限アフィン被覆上で生成元を持ち上げれば、有限型のイデアル層の模型を得る。 -/
theorem exists_finiteType_ideal_model_of_affine_generators
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsAffineHom f] (K : X.IdealSheafData)
    {ι : Type u} [Finite ι] (U : ι → Y.affineOpens)
    (hU : ⨆ i, (U i).1 = ⊤) (s : ∀ i, Finset Γ(Y, (U i).1))
    (hs : ∀ i x, x ∈ s i → x ∈ (K.map f).ideal (U i))
    (hgen : ∀ i, (Ideal.span (s i : Set Γ(Y, (U i).1))).map (f.app (U i).1).hom =
      K.ideal ⟨f ⁻¹ᵁ (U i).1, (U i).2.preimage f⟩) :
    ∃ J : Y.IdealSheafData, IsFiniteTypeIdealSheaf J ∧ J.comap f = K := by
  obtain ⟨J, hJK, hJ, hmem⟩ :=
    exists_finiteType_subideal_containing_affine_sections (K.map f) U s hs
  refine ⟨J, hJ, le_antisymm ?_ ?_⟩
  · exact (Scheme.IdealSheafData.comap_mono f hJK).trans (K.comap_map_le f)
  · apply Scheme.IdealSheafData.le_of_iSup_eq_top
      (fun i ↦ ⟨f ⁻¹ᵁ (U i).1, (U i).2.preimage f⟩) (f.iSup_preimage_eq_top hU)
    intro i
    rw [← hgen i]
    refine (Ideal.map_mono (Ideal.span_le.mpr (hmem i))).trans ?_
    rw [Ideal.map_le_iff_le_comap]
    have h := J.le_map_comap f (U i)
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at h
    exact h

/-- 有限被覆上の有限生成イデアルの像が K なら、その有限型イデアル層の模型を得る。 -/
theorem exists_finiteType_ideal_model_of_affine_ideal_models
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsAffineHom f] (K : X.IdealSheafData)
    {ι : Type u} [Finite ι] (U : ι → Y.affineOpens)
    (hU : ⨆ i, (U i).1 = ⊤) (L : ∀ i, Ideal Γ(Y, (U i).1))
    (hL : ∀ i, (L i).FG)
    (heq : ∀ i, (L i).map (f.app (U i).1).hom =
      K.ideal ⟨f ⁻¹ᵁ (U i).1, (U i).2.preimage f⟩) :
    ∃ J : Y.IdealSheafData, IsFiniteTypeIdealSheaf J ∧ J.comap f = K := by
  classical
  choose s hs using hL
  apply exists_finiteType_ideal_model_of_affine_generators f K U hU s
  · intro i x hx
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom, Ideal.mem_comap, ← heq i]
    exact Ideal.mem_map_of_mem _ ((hs i) ▸ Ideal.subset_span hx)
  · intro i
    rw [hs i]
    exact heq i

end SerrePositivity.AlgebraicGeometry
