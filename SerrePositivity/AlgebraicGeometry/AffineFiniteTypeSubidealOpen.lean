module

public import SerrePositivity.AlgebraicGeometry.AffineFiniteTypeSubidealFamily
public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSheafOpenCover
public import SerrePositivity.AlgebraicGeometry.IdealSheafOpenCoverExt

/-!
概要：アフィン基底の準コンパクト開上での一致を保つ有限型部分イデアルを選ぶ。
方針：その開を有限個のアフィン開で覆い、有限族の切断イデアルの一致を使う。
規約：基底の Noether 性は不要。
使われ方：Stacks 01PF の一般の基底への有限型延長の帰納。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

set_option backward.isDefEq.respectTransparency false in
/-- アフィン基底で、準コンパクト開への制限を保つ有限型部分イデアル層を選ぶ。 -/
theorem exists_finiteType_subideal_eq_on_quasiCompact_open_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (K : X.IdealSheafData) (W : X.Opens)
    (hW : IsCompact (W : Set X)) (hK : IsFiniteTypeIdealSheaf (K.comap W.ι)) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ IsFiniteTypeIdealSheaf J ∧
      J.comap W.ι = K.comap W.ι := by
  classical
  obtain ⟨Us, hUs, hfinite, hcover⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact hW
  letI : Finite Us := hfinite.to_subtype
  let U (i : Us) : X.affineOpens := ⟨i.1, hUs i.2⟩
  have hle (i : Us) : (U i).1 ≤ W := by
    rw [hcover]
    exact le_sSup i.2
  have hfg (i : Us) : (K.ideal (U i)).FG := by
    have hlocal : IsFiniteTypeIdealSheaf (K.comap (U i).1.ι) := by
      rw [← X.homOfLE_ι (hle i), Scheme.IdealSheafData.comap_comp]
      exact hK.comap_openImmersion _
    exact fg_ideal_of_comap_opens_top K (U i) (hlocal _)
  obtain ⟨J, hJK, hJ, heq⟩ :=
    exists_finiteType_subideal_eq_on_affine_family_of_isAffine K U hfg
  refine ⟨J, hJK, hJ, ?_⟩
  let 𝒰 : W.toScheme.OpenCover := Scheme.Cover.mkOfCovers Us
    (fun i ↦ (U i).1.toScheme) (fun i ↦ X.homOfLE (hle i)) (by
      intro x
      have hx : x.1 ∈ sSup Us := hcover ▸ x.2
      obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
      exact ⟨⟨V, hV⟩, ⟨x.1, hxV⟩, Subtype.ext (X.homOfLE_apply _ _)⟩)
  apply idealSheaf_ext_of_openCover 𝒰
  intro i
  change (J.comap W.ι).comap (X.homOfLE (hle i)) =
    (K.comap W.ι).comap (X.homOfLE (hle i))
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    X.homOfLE_ι]
  exact (idealSheaf_comap_eq_iff_affine_sections J K (U i)).mpr (heq i)

end SerrePositivity.AlgebraicGeometry
