module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterBFComparison

/-!
概要：符号付き loop の BF 比較を、指定した部分パラメータの持ち上げと両立させる。
方針：元の全 Hom の後合成の相対 RLP と垂直ホモトピー延長を実際の BF 射影に適用する。
規約：置換前の厳密化の射影を固定。使われ方：BF 持ち上げの選択と高次パラメータの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 指定した全 Hom の部分族を厳密に保つ、符号付き loop の BF 比較の持ち上げ。 -/
def kanAdjointParameterBFRelativeLift (X Y : OmegaSpectrum.{u})
    {B : PointedSimplicialSet.{u}} (j : B ⟶ pointedSpace X Y.toKanSequence) [Mono j.right]
    (a : B ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence)
    (h : a ≫ pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
      j ≫ kanAdjointParameterRectification X Y) :
    { l : pointedSpace X Y.toKanSequence ⟶
        pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence //
      j ≫ l = a ∧ l ≫ pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
        kanAdjointParameterRectification X Y } :=
  pointedPostRelativeLift X (OmegaSpectrum.signedLoopProjection Y)
    (signedLoopProjection_level_rlp Y) j a (kanAdjointParameterRectification X Y) h

/-- BF 射影が同じ二つの全パラメータ比較を、元の指定した垂直ホモトピーを保って比較する。 -/
lemma kanAdjointParameterBF_homotopy_extension (X Y : OmegaSpectrum.{u})
    {B : PointedSimplicialSet.{u}} (j : B ⟶ pointedSpace X Y.toKanSequence) [Mono j.right]
    (f g : pointedSpace X Y.toKanSequence ⟶
      pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence)
    (hf : f ≫ pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
      kanAdjointParameterRectification X Y)
    (hg : g ≫ pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
      kanAdjointParameterRectification X Y)
    (V : SSet.Homotopy (j.right ≫ f.right) (j.right ≫ g.right))
    (hbase : B.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
        (pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence).hom)
    (hvertical : V.h ≫ (pointedPost X (OmegaSpectrum.signedLoopProjection Y)).right =
      fst B.right (Δ[1] : SSet.{u}) ≫ j.right ≫
        (kanAdjointParameterRectification X Y).right) :
    ∃ H : SSet.Homotopy f.right g.right,
      H.h ≫ (pointedPost X (OmegaSpectrum.signedLoopProjection Y)).right =
        fst (pointedSpace X Y.toKanSequence).right (Δ[1] : SSet.{u}) ≫
          (kanAdjointParameterRectification X Y).right ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h = V.h ∧
      (pointedSpace X Y.toKanSequence).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence).hom := by
  have hfp := congrArg Under.Hom.right hf
  change f.right ≫ (pointedPost X (OmegaSpectrum.signedLoopProjection Y)).right =
    (kanAdjointParameterRectification X Y).right at hfp
  have hv : V.h ≫ (pointedPost X (OmegaSpectrum.signedLoopProjection Y)).right =
      fst B.right (Δ[1] : SSet.{u}) ≫ j.right ≫ f.right ≫
        (pointedPost X (OmegaSpectrum.signedLoopProjection Y)).right := by
    rw [hfp]
    exact hvertical
  obtain ⟨H, hH, hJ, hB⟩ := pointedPost_homotopy_extension X
    (OmegaSpectrum.signedLoopProjection Y) (signedLoopProjection_level_rlp Y)
    j f g (hf.trans hg.symm) V hbase hv
  rw [hfp] at hH
  exact ⟨H, hH, hJ, hB⟩

end SerrePositivity.KST.Spectra.RawSpectrumMapping
