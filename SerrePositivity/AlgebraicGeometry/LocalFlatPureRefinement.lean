module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalDominationRestriction
public import SerrePositivity.AlgebraicGeometry.OpenCenterExtension
public import SerrePositivity.AlgebraicGeometry.AdmissibleRefinement
public import SerrePositivity.AlgebraicGeometry.PureTransformOpenLocality

/-!
概要：KST §5、Stacks 0815 の有限アフィン被覆上の局所平坦化中心を共通細分でまとめる。
方針：局所中心を全体へ延長し、共通細分の開逆像から局所 blowup への実際の射を作る。
規約：局所の純変換の平坦性は証明された全アフィン引き戻しの性質として入力する。
使われ方：有限加群の平坦化中心の大域化。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限アフィン被覆の admissible な局所平坦化を一つの大域中心の blowup 上で保つ。
方針：延長中心の有限共通細分から局所対象への射を作り、引き戻しの平坦性を開被覆で貼り合わせる。
規約：KST §5、Stacks 0815、大域中心の補開集合は指定された U に一致する。
使われ方：最初の blowup 上の局所平坦化中心を一つにまとめる。
-/
theorem exists_admissible_flatPure_refinement {R : CommRingCat.{u}} {S : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsNoetherian S] (p : S ⟶ Spec R) (f : R)
    (M : Type v) [AddCommGroup M] [Module R M] (U : S.Opens)
    (𝒰 : S.AffineOpenCover) [Finite 𝒰.I₀]
    (L : ∀ i, (Spec (𝒰.X i)).IdealSheafData)
    (hL : ∀ i, IsUAdmissibleCenter (𝒰.f i ⁻¹ᵁ U) (L i))
    (hflat : ∀ i, HasFlatPurePullbacks
      (affineBlowupπ (specIdealEquiv (𝒰.X i) (L i)) ≫ 𝒰.f i ≫ p) f M) :
    ∃ K : S.IdealSheafData, centerComplement K = U ∧
      (∀ V : S.affineOpens, (K.ideal V).FG) ∧
      HasFlatPurePullbacks (blowupπ K ≫ p) f M := by
  classical
  let N (i : 𝒰.I₀) := (L i).map (𝒰.f i)
  have hN (i : 𝒰.I₀) : IsUAdmissibleCenter U (N i) :=
    isUAdmissibleCenter_map (𝒰.f i) U (L i) (hL i)
  obtain ⟨K, hKU, hKfg, hK⟩ := exists_admissible_family_refinement U N hN
  choose τ hτ using hK
  let Y (i : 𝒰.I₀) := affineBlowup (specIdealEquiv (𝒰.X i) (L i))
  let s (i : 𝒰.I₀) : Y i ⟶ S := affineBlowupπ (specIdealEquiv (𝒰.X i) (L i)) ≫ 𝒰.f i
  have hlocal (i : 𝒰.I₀) :
      ∃ q : (blowupπ K ⁻¹ᵁ (𝒰.f i).opensRange).toScheme ⟶ Y i,
        q ≫ s i = (blowupπ K ⁻¹ᵁ (𝒰.f i).opensRange).ι ≫ blowupπ K := by
    have hgi : ∃ gi : affineBlowup (specIdealEquiv (𝒰.X i) ((N i).comap (𝒰.f i))) ⟶ Y i,
        gi ≫ s i = affineBlowupπ (specIdealEquiv (𝒰.X i) ((N i).comap (𝒰.f i))) ≫ 𝒰.f i := by
      have he : (N i).comap (𝒰.f i) = L i :=
        idealSheaf_comap_map_openImmersion (𝒰.f i) (L i)
      let P (Q : (Spec (𝒰.X i)).IdealSheafData) : Prop :=
        ∃ gi : affineBlowup (specIdealEquiv (𝒰.X i) Q) ⟶ Y i,
          gi ≫ s i = affineBlowupπ (specIdealEquiv (𝒰.X i) Q) ≫ 𝒰.f i
      exact (congrArg P he).mpr ⟨𝟙 _, by simp [s]⟩
    obtain ⟨gi, hgi⟩ := hgi
    exact ⟨localDominationRestriction K (N i) (𝒰.f i) (τ i) (hτ i) gi,
      localDominationRestriction_base K (N i) (𝒰.f i) (τ i) (hτ i) (s i) gi hgi⟩
  choose q hq using hlocal
  let W (i : 𝒰.I₀) := blowupπ K ⁻¹ᵁ (𝒰.f i).opensRange
  have hW : (⨆ i, W i) = ⊤ := by
    apply top_unique
    intro x _
    have hx : blowupπ K x ∈ (⨆ i, (𝒰.f i).opensRange) := by
      rw [show (⨆ i, (𝒰.f i).opensRange) = ⊤ from 𝒰.openCover.iSup_opensRange]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let 𝒱 := Scheme.openCoverOfIsOpenCover (blowup K) W hW
  refine ⟨K, hKU, hKfg, ?_⟩
  apply hasFlatPurePullbacks_of_openCover (blowupπ K ≫ p) f M 𝒱
  intro i
  have heq : q i ≫ (affineBlowupπ (specIdealEquiv (𝒰.X i) (L i)) ≫ 𝒰.f i ≫ p) =
      (W i).ι ≫ (blowupπ K ≫ p) := by
    change q i ≫ (s i ≫ p) = _
    rw [← Category.assoc, hq i, Category.assoc]
  exact (congrArg (fun t => HasFlatPurePullbacks t f M) heq).mp ((hflat i).comp (q i))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
