module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalDominationRestriction
public import SerrePositivity.AlgebraicGeometry.DenseOpenGluing
public import SerrePositivity.AlgebraicGeometry.AdmissibleRefinement
public import SerrePositivity.AlgebraicGeometry.BlowupSchemeDensity

/-!
概要：KST §5、Stacks 080Y の有限アフィン被覆上の admissible 支配の大域化。
方針：局所中心を全体へ延長し、中心外をちょうど U とする共通細分から局所支配射を貼り合わせる。
規約：入力の局所支配射も出力の大域射も実際のスキーム射で与える。
使われ方：アフィン基底での合成支配・平坦化を一般 Noether 基底へ移す。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限アフィン被覆上で U-admissible blowup により支配される分離な射は、一つの大域 blowup で支配される。
方針：中心の延長と有限共通細分を構成し、U のスキーム論的稠密性で局所射を貼り合わせる。
規約：KST §5、Stacks 080Y、基底は Noether、標的射は U 上で同型。
使われ方：局所的な合成支配・平坦化の大域化。
-/
theorem exists_domination_of_finite_affine_local {S Y : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsNoetherian S] (s : Y ⟶ S) [IsSeparated s]
    (U : S.Opens) [IsIso (s ∣_ U)] (𝒰 : S.AffineOpenCover) [Finite 𝒰.I₀]
    (L : ∀ i, (Spec (𝒰.X i)).IdealSheafData)
    (hL : ∀ i, IsUAdmissibleCenter (𝒰.f i ⁻¹ᵁ U) (L i))
    (g : ∀ i, affineBlowup (specIdealEquiv (𝒰.X i) (L i)) ⟶ Y)
    (hg : ∀ i, g i ≫ s = affineBlowupπ (specIdealEquiv (𝒰.X i) (L i)) ≫ 𝒰.f i) :
    ∃ M : S.IdealSheafData, centerComplement M = U ∧
      (∀ V : S.affineOpens, (M.ideal V).FG) ∧ ∃ G : blowup M ⟶ Y, G ≫ s = blowupπ M := by
  classical
  let N (i : 𝒰.I₀) := (L i).map (𝒰.f i)
  have hN (i : 𝒰.I₀) : IsUAdmissibleCenter U (N i) :=
    isUAdmissibleCenter_map (𝒰.f i) U (L i) (hL i)
  obtain ⟨M, hMU, hMfg, hM⟩ := exists_admissible_family_refinement U N hN
  choose τ hτ using hM
  have hlocal (i : 𝒰.I₀) : ∃ q : (blowupπ M ⁻¹ᵁ (𝒰.f i).opensRange).toScheme ⟶ Y,
      q ≫ s = (blowupπ M ⁻¹ᵁ (𝒰.f i).opensRange).ι ≫ blowupπ M := by
    have hgi : ∃ gi : affineBlowup (specIdealEquiv (𝒰.X i) ((N i).comap (𝒰.f i))) ⟶ Y,
        gi ≫ s = affineBlowupπ (specIdealEquiv (𝒰.X i) ((N i).comap (𝒰.f i))) ≫ 𝒰.f i := by
      have he : (N i).comap (𝒰.f i) = L i :=
        idealSheaf_comap_map_openImmersion (𝒰.f i) (L i)
      let P (Q : (Spec (𝒰.X i)).IdealSheafData) : Prop :=
        ∃ gi : affineBlowup (specIdealEquiv (𝒰.X i) Q) ⟶ Y,
          gi ≫ s = affineBlowupπ (specIdealEquiv (𝒰.X i) Q) ≫ 𝒰.f i
      exact (congrArg P he).mpr ⟨g i, hg i⟩
    obtain ⟨gi, hgi⟩ := hgi
    exact ⟨localDominationRestriction M (N i) (𝒰.f i) (τ i) (hτ i) gi,
      localDominationRestriction_base M (N i) (𝒰.f i) (τ i) (hτ i) s gi hgi⟩
  choose q hq using hlocal
  let W (i : 𝒰.I₀) := blowupπ M ⁻¹ᵁ (𝒰.f i).opensRange
  have hW : (⨆ i, W i) = ⊤ := by
    apply top_unique
    intro x _
    have hx : blowupπ M x ∈ (⨆ i, (𝒰.f i).opensRange) := by
      rw [show (⨆ i, (𝒰.f i).opensRange) = ⊤ from 𝒰.openCover.iSup_opensRange]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let 𝒱 := Scheme.openCoverOfIsOpenCover (blowup M) W hW
  have hdense : IsSchemeTheoreticallyDominant (blowupπ M ⁻¹ᵁ U).ι := by
    have := blowup_centerComplement_isSchemeTheoreticallyDominant M
    have he : blowupπ M ⁻¹ᵁ centerComplement M = blowupπ M ⁻¹ᵁ U :=
      congrArg (fun V : S.Opens => blowupπ M ⁻¹ᵁ V) hMU
    rw [← Scheme.isoOfEq_inv_ι (blowup M) he]
    infer_instance
  have hker : (blowupπ M ⁻¹ᵁ U).ι.ker = ⊥ := Scheme.Hom.ker_eq_bot _
  exact ⟨M, hMU, hMfg, denseOpenGlue s U (blowupπ M) hker 𝒱 q hq,
    denseOpenGlue_base s U (blowupπ M) hker 𝒱 q hq⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
