module


public meta import SerrePositivity.Util.Citation
public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BlowupOpenMap
public import SerrePositivity.AlgebraicGeometry.AffineAdmissibleComposition
public import SerrePositivity.AlgebraicGeometry.AffineLocalDominationGluing
public import SerrePositivity.AlgebraicGeometry.FiniteAffineCover

/-!
概要：KST §5、Stacks 080Y の一般 Noether 基底上の二段の admissible blowup の支配。
方針：有限アフィン開被覆へ制限し、アフィン合成支配の射を一般の開比較で戻して貼り合わせる。
規約：通常の blowup の実際の対象と射を使う。
使われ方：平坦化に現れる有限回の admissible blowup の合成の支配。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether 基底上の二段の U-admissible blowup は一つの U-admissible blowup で支配される。
方針：有限アフィン被覆上の合成支配を構成し、延長中心の共通細分とスキーム論的稠密性で大域化する。
規約：KST §5、Stacks 080Y、二段目の中心は U の逆像を避ける。
使われ方：有限回の admissible blowup の塔を基底上の一つの中心へ集約する。
-/
theorem exists_admissible_composition_domination {S : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsNoetherian S] (I : S.IdealSheafData)
    (K : (blowup I).IdealSheafData) (U : S.Opens)
    (hI : IsUAdmissibleCenter U I)
    (hK : IsUAdmissibleCenter (blowupπ I ⁻¹ᵁ U) K) :
    ∃ M : S.IdealSheafData, (∀ V : S.affineOpens, (M.ideal V).FG) ∧
      IsUAdmissibleCenter U M ∧ ∃ g : blowup M ⟶ blowup K,
        g ≫ blowupπ K ≫ blowupπ I = blowupπ M := by
  classical
  obtain ⟨𝒰, hfinite⟩ := exists_finite_affineOpenCover S
  let : Finite 𝒰.I₀ := hfinite
  let s := blowupπ K ≫ blowupπ I
  have : IsSeparated s := by dsimp only [s]; infer_instance
  have : IsIso (s ∣_ U) := by
    have := blowupπ_restrict_admissible_isIso U I hI
    have := blowupπ_restrict_admissible_isIso (blowupπ I ⁻¹ᵁ U) K hK
    dsimp only [s]
    rw [morphismRestrict_comp]
    infer_instance
  have hlocal (i : 𝒰.I₀) : ∃ L : (Spec (𝒰.X i)).IdealSheafData,
      IsUAdmissibleCenter (𝒰.f i ⁻¹ᵁ U) L ∧
      ∃ g : affineBlowup (specIdealEquiv (𝒰.X i) L) ⟶ blowup K,
        g ≫ s = affineBlowupπ (specIdealEquiv (𝒰.X i) L) ≫ 𝒰.f i := by
    let Ii := specIdealEquiv (𝒰.X i) (I.comap (𝒰.f i))
    let qi := blowupAffineOpenMap (𝒰.f i) I
    let Ki := K.comap qi
    let Ui := 𝒰.f i ⁻¹ᵁ U
    have hNoeth : IsLocallyNoetherian (Spec (𝒰.X i)) :=
      isLocallyNoetherian_of_isOpenImmersion (𝒰.f i)
    have : IsNoetherianRing (𝒰.X i) := isLocallyNoetherian_Spec.mp hNoeth
    have hIi : Ui ≤ affineCenterComplement Ii := by
      change 𝒰.f i ⁻¹ᵁ U ≤ affineCenterComplement (specIdealEquiv (𝒰.X i) (I.comap (𝒰.f i)))
      rw [← affine_preimage_centerComplement]
      exact fun x hx => hI hx
    have hKi : affineBlowupπ Ii ⁻¹ᵁ Ui ≤ centerComplement Ki := by
      change affineBlowupπ Ii ⁻¹ᵁ (𝒰.f i ⁻¹ᵁ U) ≤ centerComplement (K.comap qi)
      rw [← preimage_centerComplement_comap, ← Scheme.Hom.comp_preimage,
        ← blowupAffineOpenMap_base, Scheme.Hom.comp_preimage]
      exact fun x hx => hK hx
    obtain ⟨J, _, hJU, gi, hgi⟩ := exists_affine_admissible_composition_domination Ii Ki Ui hIi hKi
    have hqi : qi ≫ blowupπ I = affineBlowupπ Ii ≫ 𝒰.f i :=
      blowupAffineOpenMap_base (𝒰.f i) I
    have hgplain : (gi ≫ blowupOpenMap K qi) ≫ s = affineBlowupπ J ≫ 𝒰.f i := by
      calc
        _ = (gi ≫ blowupπ Ki ≫ affineBlowupπ Ii) ≫ 𝒰.f i := by
          dsimp only [s]
          simp only [Category.assoc, blowupOpenMap_base_assoc, hqi]
          rfl
        _ = _ := congrArg (· ≫ 𝒰.f i) hgi
    let Q := (specIdealEquiv (𝒰.X i)).symm J
    have hQ : specIdealEquiv (𝒰.X i) Q = J := OrderIso.apply_symm_apply _ _
    refine ⟨Q, ?_, ?_⟩
    · change Ui ≤ centerComplement Q
      rw [centerComplement_specIdealEquiv, hQ]
      exact hJU
    · let P (A : Ideal (𝒰.X i)) : Prop := ∃ g : affineBlowup A ⟶ blowup K,
        g ≫ s = affineBlowupπ A ≫ 𝒰.f i
      exact (congrArg P hQ).mpr ⟨gi ≫ blowupOpenMap K qi, hgplain⟩
  choose L hL g hg using hlocal
  obtain ⟨M, hMU, hMfg, G, hG⟩ :=
    exists_domination_of_finite_affine_local s U 𝒰 L hL g hg
  refine ⟨M, hMfg, ?_, G, ?_⟩
  · change U ≤ centerComplement M
    rw [hMU]
  · simpa only [s] using hG

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

@[deprecated (since := "2026-11-07")]
deprecated_alias_util _root_.SerrePositivity.KST.SchemeLemmas.exists_admissible_composition_domination := _root_.SerrePositivity.AlgebraicGeometry.exists_admissible_composition_domination

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Claim 5.3" (partial := component) "仮定：二段の許容ブローアップが与えられる（Lean が強い）。結論：一つの許容ブローアップで支配する幾何部分。通常ブローアップの (†) からの K の正方形の比較・帰結は含まない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.exists_admissible_composition_domination
attribute [cite KST "Proof step §5.2 flattening" (partial := component) "仮定：有限射の場合の平坦化、または既に与えた二段の許容ブローアップ（Lean が強い）。結論：有限射からの精密化と許容ブローアップの支配。一般の固有射の Temkin による支配を供給しない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.exists_admissible_composition_domination
attribute [cite KST "Prop 5.4" (partial := component) "仮定：二段の許容ブローアップが与えられる（Lean が強い）。結論：一つの許容ブローアップで支配する幾何部分。通常ブローアップの (†) からの K の正方形の比較・帰結は含まない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.exists_admissible_composition_domination
attribute [cite LT "Proof step A.2 Step 3" (partial := component) "仮定：有限射、または既に与えられた二段の許容ブローアップ（Lean が強い）。結論：古典的な支配・平坦化の幾何の部品。切断型不変量に適用した引き戻しはない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.exists_admissible_composition_domination
