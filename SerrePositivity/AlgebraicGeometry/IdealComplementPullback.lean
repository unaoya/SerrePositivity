module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SpecIdeal
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway
public import SerrePositivity.AlgebraicGeometry.PrincipalDetector

/-!
概要：KST §5、Stacks 080Y のイデアル層の逆像と中心外開集合の比較。
方針：支持の逆像公式と Spec の零点集合の計算を使う。
規約：任意のスキーム射を許し、中心の被約化は行わない。
使われ方：局所的に中心を可逆化する射の零核の中心外検出。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

/--
概要：中心外開集合はイデアル層の逆像と両立する。
方針：逆像中心の支持の公式を補集合へ移す。
規約：KST §5、Stacks 080Y、任意のスキーム射。
使われ方：局所チャートの中心外条件を一般の基底へ移す。
-/
theorem preimage_centerComplement_comap {X Y : Scheme.{u}} (K : Y.IdealSheafData)
    (f : X ⟶ Y) : f ⁻¹ᵁ centerComplement K = centerComplement (K.comap f) := by
  ext x
  change (f x ∉ K.support) ↔ x ∉ (K.comap f).support
  rw [Scheme.IdealSheafData.support_comap]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
概要：Spec 上のイデアル層の中心外開集合は対応する環イデアルの中心外開集合。
方針：全空間のアフィン切断で支持を計算し、Spec の零点集合の公式を使う。
規約：KST §5、Stacks 080Y、ΓSpec 同型の逆像を明示する。
使われ方：環論的な単項中心の中心外検出を幾何学的に読む。
-/
theorem centerComplement_specIdealEquiv (A : CommRingCat.{u}) (K : (Spec A).IdealSheafData) :
    centerComplement K = affineCenterComplement (specIdealEquiv A K) := by
  ext x
  change (x ∉ K.support) ↔ (x : PrimeSpectrum A) ∈ affineCenterComplement (specIdealEquiv A K)
  rw [mem_affineCenterComplement]
  change (x ∉ K.support) ↔ x ∉ PrimeSpectrum.zeroLocus (specIdealEquiv A K : Set A)
  rw [K.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top _⟩) (Set.mem_univ x),
    Spec_zeroLocus]
  rfl

/--
概要：任意のアフィン局所射での中心外開集合の逆像を環イデアルから計算する。
方針：一般の支持の逆像と Spec の中心外公式を合成する。
規約：KST §5、Stacks 080Y、局所射が開埋め込みである必要はない。
使われ方：正則単項の逆像中心からの中心外検出。
-/
theorem affine_preimage_centerComplement {X : Scheme.{u}} {A : CommRingCat.{u}}
    (K : X.IdealSheafData) (j : Spec A ⟶ X) :
    j ⁻¹ᵁ centerComplement K = affineCenterComplement (specIdealEquiv A (K.comap j)) := by
  rw [preimage_centerComplement_comap, centerComplement_specIdealEquiv]

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所射の像中心に属する b を可逆化した検出射は一般の中心の外に入る。
方針：環イデアルの中心外検出とアフィン逆像中心の支持公式を使う。
規約：KST §5、Stacks 080Y、b の正則性はこの像の包含には不要。
使われ方：正則な b の局所化で普遍写像の局所的一意性を検出する。
-/
theorem local_principalDetector_range {X : Scheme.{u}} {A B : CommRingCat.{u}}
    (K : X.IdealSheafData) (j : Spec A ⟶ X) (φ : A ⟶ B) (b : B)
    (hb : b ∈ (specIdealEquiv A (K.comap j)).map φ.hom) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫
      Spec.map φ ≫ j) ⊆ (centerComplement K).carrier := by
  rintro _ ⟨x, rfl⟩
  have hx := principalDetector_range_complement (specIdealEquiv A (K.comap j)) φ.hom b hb
    ⟨x, rfl⟩
  rw [← affine_preimage_centerComplement K j] at hx
  exact hx

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
