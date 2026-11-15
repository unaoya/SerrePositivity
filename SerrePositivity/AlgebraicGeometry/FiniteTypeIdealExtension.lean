module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealFiniteFamilyExtension

/-!
概要：準コンパクト開上の有限型部分イデアル層を qcqs スキーム全体へ延長する。
方針：有限アフィン被覆に前の有限族の延長を適用し、有限型性を被覆で判定する。
規約：Stacks 01PF (28.23.2) のイデアル層の場合。Noether 性は不要。
使われ方：C02 の有限表示閉包絡の存在。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 準コンパクト開上の有限型部分イデアル層を、同じ大域イデアルの中で延長する。 -/
theorem exists_finiteType_subideal_extension
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) (W : X.Opens) (hW : IsCompact (W : Set X))
    (H : W.toScheme.IdealSheafData) (hHK : H ≤ K.comap W.ι)
    (hH : IsFiniteTypeIdealSheaf H) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ IsFiniteTypeIdealSheaf J ∧ J.comap W.ι = H := by
  classical
  obtain ⟨Us, hUs, hfinite, hcover⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  letI : Fintype Us := hfinite.fintype
  let U (i : Us) : X.affineOpens := ⟨i.1, hUs i.2⟩
  have htop : ⨆ i, (U i).1 = ⊤ := by
    calc
      _ = sSup Us := le_antisymm (iSup_le fun i ↦ le_sSup i.2)
        (sSup_le fun V hV ↦ le_iSup_of_le ⟨V, hV⟩ le_rfl)
      _ = ⊤ := hcover.symm
  obtain ⟨J, hJK, hJW, hJU⟩ :=
    exists_subideal_finiteType_on_finite_affine_family_extending K W hW H hHK hH U Finset.univ
  refine ⟨J, hJK, ?_, hJW⟩
  apply isFiniteTypeIdealSheaf_of_affineCover J U htop
  intro i
  exact fg_ideal_of_comap_opens_top J (U i) ((hJU i (Finset.mem_univ i)) _)

end SerrePositivity.AlgebraicGeometry
