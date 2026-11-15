module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealExtension
public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSheafLocality

/-!
概要：アフィン開上の有限個のイデアル切断を含む有限型部分イデアル層を作る。
方針：有限生成イデアルを topIso でアフィン開の全体切断へ移し、01PF の延長を使う。
規約：基底は qcqs。Noether 性は不要。
使われ方：C02 の有限表示閉包絡で支持を指定した開へ収める。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false in
/-- アフィン開上の有限個の切断を、大域の有限型部分イデアル層に含める。 -/
theorem exists_finiteType_subideal_containing_affine_finset
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) (U : X.affineOpens) (s : Finset Γ(X, U.1))
    (hs : ∀ x ∈ s, x ∈ K.ideal U) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ IsFiniteTypeIdealSheaf J ∧
      ∀ x ∈ s, x ∈ J.ideal U := by
  classical
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  let I : Ideal Γ(U.1, ⊤) := (Ideal.span (s : Set Γ(X, U.1))).map e.symm
  have hI : I.FG := (show (Ideal.span (s : Set Γ(X, U.1))).FG from ⟨s, rfl⟩).map _
  let E := Scheme.IdealSheafData.equivOfIsAffine (X := U.1.toScheme)
  let H := E.symm I
  have htop : H.ideal ⟨⊤, isAffineOpen_top U⟩ = I := E.apply_symm_apply I
  have hHK : H ≤ K.comap U.1.ι := by
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [htop, idealSheaf_comap_opens_top]
    exact Ideal.map_mono (Ideal.span_le.mpr hs)
  have hH : IsFiniteTypeIdealSheaf H :=
    isFiniteTypeIdealSheaf_of_fg_top H (htop.symm ▸ hI)
  obtain ⟨J, hJK, hJ, hJU⟩ :=
    exists_finiteType_subideal_extension K U.1 U.2.isCompact H hHK hH
  have hJtop : (J.ideal U).map e.symm = I := by
    have h := congrArg (fun L : U.1.toScheme.IdealSheafData ↦
      L.ideal ⟨⊤, isAffineOpen_top U⟩) hJU
    rw [idealSheaf_comap_opens_top, htop] at h
    exact h
  refine ⟨J, hJK, hJ, ?_⟩
  intro x hx
  have hmem : e.symm x ∈ (J.ideal U).map e.symm := by
    rw [hJtop]
    exact Ideal.mem_map_of_mem e.symm (Ideal.subset_span hx)
  exact Ideal.apply_mem_of_equiv_iff.mp hmem

end SerrePositivity.AlgebraicGeometry
