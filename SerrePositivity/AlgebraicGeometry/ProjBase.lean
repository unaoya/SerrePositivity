module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
概要：KST §5 の blowup の構造射に必要な Proj の零次成分上の局所計算。
方針：Mathlib の局所環付き空間としての Proj とスキームとしての Proj を比較する。
規約：次数は自然数、斉次成分は加法部分群をなす。
使われ方：構造射による基礎環の基本開集合の逆像を計算する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

set_option backward.isDefEq.respectTransparency false in
/--
概要：Proj の基本開集合から Spec へのスキーム射は局所環付き空間の構成と一致する。
方針：Γ と Spec の随伴による射の公式を両方の構成に適用する。
規約：KST §5、基本開集合を指定する元の正次数性は要求しない。
使われ方：零次成分に関する点と基本開集合の計算をスキームへ移す。
-/
lemma proj_basicOpenToSpec_forget (f : A) :
    Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec 𝒜 f) =
      ProjectiveSpectrum.Proj.toSpec 𝒜 f := by
  unfold ProjectiveSpectrum.Proj.toSpec
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
概要：Proj の基本開集合から Spec への射での素イデアルへの所属を計算する。
方針：斉次分数の分子による所属判定を局所環付き空間の実装から移す。
規約：KST §5、分子と分母は同じ次数を持つ。
使われ方：blowup 構造射の基本開集合の逆像の記述。
-/
lemma proj_basicOpenToSpec_mk_mem (f : A) (x : (Proj.basicOpen 𝒜 f).toScheme)
    (t : NumDenSameDeg 𝒜 (.powers f)) :
    mk t ∈ ((Proj.basicOpenToSpec 𝒜 f) x).asIdeal ↔
      t.num.1 ∈ x.1.asHomogeneousIdeal := by
  have h := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x t
  rw [← proj_basicOpenToSpec_forget 𝒜 f] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/--
概要：Proj の構造射が与える零次成分の素イデアルは斉次素イデアルとの交わり。
方針：D₊(1) 上の分母一の分数の所属判定を使う。
規約：KST §5、零次成分の元 r を環全体の元としても扱う。
使われ方：中心の補開集合の逆像を Proj の基本開集合で記述する。
-/
lemma proj_toSpecZero_mem (x : Proj 𝒜) (r : 𝒜 0) :
    r ∈ (Proj.toSpecZero 𝒜 x).asIdeal ↔ r.1 ∈ x.asHomogeneousIdeal := by
  let u : (Proj.basicOpen 𝒜 1).toScheme :=
    (Scheme.isoOfEq _ (Proj.basicOpen_one 𝒜)).inv ((Scheme.topIso _).inv x)
  have hu : u.1 = x := by
    change ((Proj.basicOpen 𝒜 1).ι)
      ((Scheme.isoOfEq _ (Proj.basicOpen_one 𝒜)).inv ((Scheme.topIso _).inv x)) = x
    rw [← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι]
    change (Scheme.topIso _).hom ((Scheme.topIso _).inv x) = x
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  change mk ⟨0, r, 1, Submonoid.one_mem _⟩ ∈
    ((Proj.basicOpenToSpec 𝒜 1) u).asIdeal ↔ _
  rw [proj_basicOpenToSpec_mk_mem, hu]

/--
概要：基礎環の基本開集合の Proj 構造射による逆像は同じ元の斉次基本開集合。
方針：素イデアルへの所属判定の否定を取る。
規約：KST §5、元 r は零次成分に属する。
使われ方：blowup の中心の補開集合上での制限。
-/
theorem proj_toSpecZero_preimage_basicOpen (r : 𝒜 0) :
    Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen r = Proj.basicOpen 𝒜 r.1 := by
  ext x
  exact not_congr (proj_toSpecZero_mem 𝒜 x r)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
