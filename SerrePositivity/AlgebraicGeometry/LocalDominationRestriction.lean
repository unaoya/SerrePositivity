module

public import SerrePositivity.AlgebraicGeometry.BlowupOpenComparison

/-!
概要：KST §5、Stacks 080Y の大域共通細分からアフィン局所支配射への制限。
方針：基底上の比較射を開逆像へ持ち上げ、アフィン開 blowup 同型の逆を合成する。
規約：実際の射と基底上の交換式を構成する。
使われ方：局所的な admissible 支配射の大域貼り合わせ。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {S Y : Scheme.{u}} {A : CommRingCat.{u}}
  (M N : S.IdealSheafData) (j : Spec A ⟶ S) [IsOpenImmersion j]
  (τ : blowup M ⟶ blowup N) (hτ : τ ≫ blowupπ N = blowupπ M)

/--
概要：基底上の blowup 比較射を基底の開集合の逆像へ制限する。
方針：構造射の交換式から開像への包含を示して開包含へ持ち上げる。
規約：KST §5、Stacks 080Y、開集合は j の像。
使われ方：大域共通細分からアフィン局所モデルへ移る。
-/
def blowupMapRestrictRange : (blowupπ M ⁻¹ᵁ j.opensRange).toScheme ⟶
    (blowupπ N ⁻¹ᵁ j.opensRange).toScheme :=
  IsOpenImmersion.lift (blowupπ N ⁻¹ᵁ j.opensRange).ι
    ((blowupπ M ⁻¹ᵁ j.opensRange).ι ≫ τ) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      change (τ ≫ blowupπ N) x.1 ∈ j.opensRange
      rw [hτ]
      exact x.2)

/--
概要：開逆像へ制限した比較射は元の射へ因子化する。
方針：開埋め込みへの持ち上げの因子化式を使う。
規約：KST §5、Stacks 080Y、元の blowup N への射。
使われ方：制限後の構造射の交換式。
-/
@[reassoc] theorem blowupMapRestrictRange_ι :
    blowupMapRestrictRange M N j τ hτ ≫ (blowupπ N ⁻¹ᵁ j.opensRange).ι =
      (blowupπ M ⁻¹ᵁ j.opensRange).ι ≫ τ :=
  IsOpenImmersion.lift_fac _ _ _

variable (s : Y ⟶ S)
  (g : affineBlowup (specIdealEquiv A (N.comap j)) ⟶ Y)
  (hg : g ≫ s = affineBlowupπ (specIdealEquiv A (N.comap j)) ≫ j)

/--
概要：大域共通細分の開逆像から、アフィン局所の支配対象への実際の射。
方針：制限した比較射、アフィン開 blowup 比較同型の逆、与えられた局所支配射を合成する。
規約：KST §5、Stacks 080Y、始域は大域の blowup M の開逆像。
使われ方：アフィン局所的な支配を大域化する局所成分。
-/
def localDominationRestriction : (blowupπ M ⁻¹ᵁ j.opensRange).toScheme ⟶ Y :=
  blowupMapRestrictRange M N j τ hτ ≫ (blowupOpenIso j N).inv ≫ g

include hg

set_option backward.isDefEq.respectTransparency false in
/--
概要：大域共通細分からの局所支配射は元の基底射と両立する。
方針：開比較同型と制限した比較射の構造射公式を順に使う。
規約：KST §5、Stacks 080Y、S への射の等式。
使われ方：稠密な中心外開集合による局所射の貼り合わせ。
-/
@[reassoc] theorem localDominationRestriction_base :
    localDominationRestriction M N j τ hτ g ≫ s =
      (blowupπ M ⁻¹ᵁ j.opensRange).ι ≫ blowupπ M := by
  unfold localDominationRestriction
  rw [Category.assoc, Category.assoc, hg, blowupOpenIso_inv_base,
    blowupMapRestrictRange_ι_assoc, hτ]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
