module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
概要：KST §5、Stacks 0815 の開被覆に従属するアフィン基本開上の持ち上げ。
方針：各点の基本開近傍を選び、開埋め込みの普遍性で実際の射を作る。
規約：環の局所化を各基本開のモデルとして使う。
使われ方：純変換の平坦性が始域の開被覆に関して局所的であること。
-/

@[expose] public noncomputable section
universe u w
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

/--
概要：アフィン試験射は各点を含むある基本開上で指定された開被覆の一つに持ち上がる。
方針：被覆の一つの逆像内に基本開近傍を取り、開埋め込みへ持ち上げる。
規約：KST §5、Stacks 0815、持ち上げと元の試験射との交換式を返す。
使われ方：局所化による平坦性の局所判定。
-/
theorem exists_basicOpen_cover_lift {X : Scheme.{u}} (𝒰 : X.OpenCover.{w})
    (A : CommRingCat.{u}) (j : Spec A ⟶ X) (x : PrimeSpectrum A) :
    ∃ (r : A) (i : 𝒰.I₀)
      (g : Spec (.of (Localization.Away r)) ⟶ 𝒰.X i),
      x ∈ PrimeSpectrum.basicOpen r ∧
      g ≫ 𝒰.f i = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))) ≫ j := by
  let i := 𝒰.idx (j x)
  let V := j ⁻¹ᵁ (𝒰.f i).opensRange
  have hx : x ∈ V := 𝒰.covers (j x)
  obtain ⟨W, ⟨r, rfl⟩, hxr, hrV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx V.isOpen
  let l := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))
  have hrange : Set.range (l ≫ j) ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨z, rfl⟩
    have hz : l z ∈ PrimeSpectrum.basicOpen r := by
      rw [← Scheme.Hom.opensRange_localizationAway r]
      exact ⟨z, rfl⟩
    exact hrV hz
  exact ⟨r, i, IsOpenImmersion.lift (𝒰.f i) (l ≫ j) hrange,
    hxr, IsOpenImmersion.lift_fac _ _ _⟩

/--
概要：開被覆への基本開上の持ち上げを単位イデアルを生成する係数族で選ぶ。
方針：各点で係数と持ち上げを選び、各点が対応する基本開に入ることから被覆性を得る。
規約：KST §5、Stacks 0815、添字は試験対象の素スペクトルの点。
使われ方：開被覆上の性質から全アフィン試験対象への平坦性を得る。
-/
theorem exists_basicOpen_cover_lifts {X : Scheme.{u}} (𝒰 : X.OpenCover.{w})
    (A : CommRingCat.{u}) (j : Spec A ⟶ X) :
    ∃ (r : PrimeSpectrum A → A) (i : PrimeSpectrum A → 𝒰.I₀)
      (g : ∀ x : PrimeSpectrum A, Spec (.of (Localization.Away (r x))) ⟶ 𝒰.X (i x)),
      Ideal.span (Set.range r) = ⊤ ∧
      ∀ x, g x ≫ 𝒰.f (i x) =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r x)))) ≫ j := by
  classical
  choose r i g hmem hg using exists_basicOpen_cover_lift 𝒰 A j
  refine ⟨r, i, g, ?_, hg⟩
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
