module

public import SerrePositivity.AlgebraicGeometry.AffineModelOpenImmersion

/-!
概要：KST §5 のアフィン局所モデルの包含に沿う比較射の像。
方針：共通基本開近傍から点を持ち上げ、像を基礎開集合の逆像と同定する。
規約：基礎スキームは任意、中心はイデアル層の切断を用いる。
使われ方：局所モデルの図式の局所的有向性と大域 blowup の構成。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意のアフィン開包含に沿うモデル比較の像は、基礎開集合の逆像全体。
方針：逆像にある点の基底で共通基本開近傍を取り、そのモデルから持ち上げる。
規約：KST §5、点集合の像を明示する。
使われ方：局所モデルの共通細分と貼り合わせの検証。
-/
theorem affineBlowupModelMap_range {U V : X.affineOpens} (h : U ≤ V) :
    Set.range (affineBlowupModelMap I h) =
      (affineBlowupModelToBase I V ⁻¹ᵁ U.1).carrier := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    change (affineBlowupModelMap I h ≫ affineBlowupModelToBase I V) x ∈ U.1
    rw [affineBlowupModelMap_toBase]
    exact affineBlowupModelToBase_mem I U x
  · intro x hx
    have hxV := affineBlowupModelToBase_mem I V x
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2
      (affineBlowupModelToBase I V x) ⟨hx, hxV⟩
    let W := X.affineBasicOpen f
    let hWU : W ≤ U := X.affineBasicOpen_le f
    let hWV : W ≤ V := hWU.trans h
    have hxg : x ∈ (affineBlowupModelToBase I V ⁻¹ᵁ X.basicOpen g).carrier := hfg ▸ hxf
    rw [← affineBlowupModelMap_range_of_eq_basicOpen I hWV g (Subtype.ext hfg)] at hxg
    obtain ⟨w, hw⟩ := hxg
    refine ⟨affineBlowupModelMap I hWU w, ?_⟩
    change (affineBlowupModelMap I hWU ≫ affineBlowupModelMap I h) w = x
    rw [affineBlowupModelMap_comp]
    exact hw

/--
概要：アフィン開包含に沿う比較射の開像は基礎開集合の逆像。
方針：開埋め込み性と点集合の像の計算を合わせる。
規約：KST §5、開部分スキームの像の等式として述べる。
使われ方：一般スキーム上の blowup の開貼り合わせ。
-/
theorem affineBlowupModelMap_opensRange {U V : X.affineOpens} (h : U ≤ V) :
    (affineBlowupModelMap I h).opensRange = affineBlowupModelToBase I V ⁻¹ᵁ U.1 :=
  TopologicalSpace.Opens.ext (affineBlowupModelMap_range I h)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
