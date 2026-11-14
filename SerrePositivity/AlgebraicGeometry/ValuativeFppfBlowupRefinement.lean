module

public import SerrePositivity.AlgebraicGeometry.ValuativeStrictTransformSurjective
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：平坦な狭義変換から、有限型 v 被覆の fppf–blowup 細分を得る。
方針：v 判定で狭義変換の全射性を供給し、Noether 基底上の有限型性を有限表示性へ渡す。
規約：元の射と fppf 因子に固有性を要求しない。
使われ方：Rydh 3.10 の Noether な段の細分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

/-- 有限型射の狭義変換の構造射も有限型。 -/
theorem strictTransformπ_finiteType_properties {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (U : S.Opens) (J : S.IdealSheafData) :
    LocallyOfFiniteType (strictTransformπ f U J) ∧ QuasiCompact (strictTransformπ f U J) := by
  unfold strictTransformπ
  constructor <;> infer_instance

/-- 平坦な狭義変換は、有限型 v 被覆の fppf–blowup 細分を与える。 -/
theorem exists_fppf_blowup_refinement_of_flat_strictTransform_vCover
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (hf : IsSchemeVCover f) (U : S.Opens) (J : S.IdealSheafData)
    (hU : Dense U.carrier) (hJ : IsUAdmissibleCenter U J)
    [Flat (strictTransformπ f U J)] :
    IsProper (blowupπ J) ∧ Surjective (blowupπ J) ∧ IsIso (blowupπ J ∣_ U) ∧
      ∃ (X' : Scheme.{u}) (g : X' ⟶ blowup J) (k : X' ⟶ X),
        Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧
          k ≫ f = g ≫ blowupπ J := by
  have hIso := blowupπ_restrict_admissible_isIso U J hJ
  have hSurj : Surjective (blowupπ J) := by
    have hrange : U.carrier ⊆ Set.range (blowupπ J) := by
      intro y hy
      obtain ⟨x, hx⟩ := (blowupπ J ∣_ U).surjective ⟨y, hy⟩
      refine ⟨x.1, ?_⟩
      calc
        blowupπ J x.1 = ((blowupπ J ⁻¹ᵁ U).ι ≫ blowupπ J) x := rfl
        _ = ((blowupπ J ∣_ U) ≫ U.ι) x :=
          congrArg (fun h => h x) (morphismRestrict_ι (blowupπ J) U).symm
        _ = y := congrArg U.ι hx
    letI : IsDominant (blowupπ J) := ⟨hU.mono hrange⟩
    infer_instance
  have hStrict := strictTransformπ_surjective_of_vCover f hf U hU J
  obtain ⟨hft, hqc⟩ := strictTransformπ_finiteType_properties f U J
  letI := hft
  letI := hqc
  exact ⟨inferInstance, hSurj, hIso, strictTransform f U J, strictTransformπ f U J,
    strictTransformToOriginal f U J, inferInstance, hStrict, inferInstance, inferInstance,
    strictTransform_square f U J⟩


end SerrePositivity.AlgebraicGeometry
