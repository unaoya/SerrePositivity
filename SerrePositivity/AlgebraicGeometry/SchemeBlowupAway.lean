module

public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAffine
public import SerrePositivity.AlgebraicGeometry.BlowupAway

/-!
概要：KST §5 の一般スキーム上の blowup の中心外同型。
方針：中心イデアル層の支持の補集合をアフィン局所化し、既存のアフィン同型を移送する。
規約：中心の厚みを保ち、支持の補開集合のみで同型を主張する。
使われ方：古典的 blowup 正方形と導来 blowup の underlying scheme との比較。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/--
概要：中心イデアル層の支持の補開集合。
方針：閉支持の開補集合を取る。
規約：KST §5、中心のスキーム構造の厚みを変えない。
使われ方：blowup の構造射が同型となる基底の開集合。
-/
def centerComplement : X.Opens := I.support.compl

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン開集合の切断環の Spec 上で、中心外開集合は切断中心の補集合。
方針：支持のアフィン局所公式と零点集合の Spec による逆像を使う。
規約：KST §5、中心の有限生成性は不要。
使われ方：アフィンの中心外同型を一般スキームへ移す。
-/
theorem fromSpec_preimage_centerComplement (U : X.affineOpens) :
    U.2.fromSpec ⁻¹ᵁ centerComplement I = affineCenterComplement (I.ideal U) := by
  ext x
  change (U.2.fromSpec x ∉ I.support) ↔ x ∈ affineCenterComplement (I.ideal U)
  rw [mem_affineCenterComplement]
  have hxU : U.2.fromSpec x ∈ U.1 := (U.2.isoSpec.inv x).2
  rw [I.mem_support_iff_of_mem hxU]
  change (x ∉ U.2.fromSpec ⁻¹' X.zeroLocus (U := U.1) (I.ideal U : Set Γ(X, U.1))) ↔ _
  rw [U.2.fromSpec_preimage_zeroLocus]

set_option backward.isDefEq.respectTransparency false in
/--
概要：構造射を両端の同型で移送しても、対応する開集合上の同型性は保たれる。
方針：同型の制限と合成の制限の公式を使う。
規約：KST §5、標的側の開集合は逆同型で引き戻す。
使われ方：アフィン blowup の中心外同型を局所モデルへ移す。
-/
theorem isIso_restrict_of_iso_comparison {A B Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (g : A ⟶ B) (e : A ≅ Y) (t : Z ≅ B)
    (h : e.hom ≫ f = g ≫ t.inv) (W : Z.Opens) [IsIso (g ∣_ t.inv ⁻¹ᵁ W)] :
    IsIso (f ∣_ W) := by
  have hc : IsIso ((e.hom ≫ f) ∣_ W) := by
    rw [h, morphismRestrict_comp]
    infer_instance
  rw [morphismRestrict_comp] at hc
  exact IsIso.of_isIso_comp_left (e.hom ∣_ f ⁻¹ᵁ W) (f ∣_ W)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の blowup の構造射は中心の補開集合上で同型。
方針：基底のアフィン開被覆上で既存のアフィンの中心外同型と比較する。
規約：KST §5、基礎スキームの分離性・Noether 性は不要。
使われ方：古典的 blowup 正方形の幾何学的入力。
-/
theorem blowupπ_restrict_complement_isIso : IsIso (blowupπ I ∣_ centerComplement I) := by
  let C := centerComplement I
  let V (U : X.affineOpens) := C.ι ⁻¹ᵁ U.1
  have hV : iSup V = ⊤ := by
    apply top_unique
    intro x _
    have hx : x.1 ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X] at hx
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) V hV
  intro U
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (blowupπ I) C (V U))]
  have heq : C.ι ''ᵁ V U = U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C) := by
    simp only [V, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_comm _ _
  rw [heq, ← (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (blowupπ I) U.1 (U.1.ι ⁻¹ᵁ C))]
  have hpre : U.2.isoSpec.inv ⁻¹ᵁ (U.1.ι ⁻¹ᵁ C) = affineCenterComplement (I.ideal U) := by
    rw [← Scheme.Hom.comp_preimage, IsAffineOpen.isoSpec_inv_ι]
    exact fromSpec_preimage_centerComplement I U
  have : IsIso (affineBlowupπ (I.ideal U) ∣_ U.2.isoSpec.inv ⁻¹ᵁ (U.1.ι ⁻¹ᵁ C)) := by
    rw [hpre]
    exact affineBlowupπ_restrict_complement_isIso (I.ideal U)
  apply isIso_restrict_of_iso_comparison (blowupπ I ∣_ U.1) (affineBlowupπ (I.ideal U))
    (blowupAffineIso I U) U.2.isoSpec _ (U.1.ι ⁻¹ᵁ C)
  exact blowupAffineIso_hom_restrict I U

/--
概要：一般の blowup の中心外開部分スキームと中心補集合の実際の同型。
方針：構造射の制限の同型性を同型として束ねる。
規約：KST §5、通常の blowup の同型。
使われ方：導来比較に渡す中心外の古典的幾何学的入力。
-/
def blowupAwayIso : (blowupπ I ⁻¹ᵁ centerComplement I).toScheme ≅
    (centerComplement I).toScheme := by
  have := blowupπ_restrict_complement_isIso I
  exact asIso (blowupπ I ∣_ centerComplement I)

/--
概要：一般の blowup の中心外同型は元の構造射と両立する。
方針：構造射の制限の包含との交換式を使う。
規約：KST §5、同型の順方向は構造射の制限。
使われ方：導来比較へ渡す中心外の射の交換式。
-/
@[reassoc] theorem blowupAwayIso_hom_ι :
    (blowupAwayIso I).hom ≫ (centerComplement I).ι =
      (blowupπ I ⁻¹ᵁ centerComplement I).ι ≫ blowupπ I :=
  morphismRestrict_ι _ _

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
