module

public import SerrePositivity.AlgebraicGeometry.ValuativeOpenImageSurjective
public import SerrePositivity.AlgebraicGeometry.FiniteTypeStrictTransformLocality
public import SerrePositivity.AlgebraicGeometry.ProperFlatBlowupRefinement
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverComposition

/-!
概要：有限型の v 被覆の狭義変換は、Noether 基底上で全射。
方針：底変換後の v 判定と、稠密開の逆像のスキーム論的閉包の全射性を使う。
規約：元の射に固有性を要求しない。
使われ方：Rydh 3.10 の fppf 因子の全射性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

/-- Noether 基底上の有限型 v 被覆の狭義変換は全射。 -/
theorem strictTransformπ_surjective_of_vCover {X S : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (hf : IsSchemeVCover f)
    (U : S.Opens) (hU : Dense U.carrier) (J : S.IdealSheafData) :
    Surjective (strictTransformπ f U J) := by
  letI := strictTransformAmbient_noetherian_of_finiteType f J
  have hp : IsSchemeVCover (pullback.snd f (blowupπ J)) :=
    IsSchemeVCover.baseChange (IsPullback.of_hasPullback f (blowupπ J)) hf
  have hs := surjective_openImage_of_vCover (pullback.snd f (blowupπ J)) hp
    (blowupπ J ⁻¹ᵁ U) (dense_preimage_blowupπ J U hU)
  change Surjective ((strictTransformOpen f U J).ι.imageι ≫ pullback.snd f (blowupπ J))
  rwa [strictTransformOpen_eq]

end SerrePositivity.AlgebraicGeometry
