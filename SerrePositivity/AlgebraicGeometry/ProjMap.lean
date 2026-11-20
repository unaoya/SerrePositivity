module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
概要：KST §5 の比較に必要な Proj の構造射の自然性。
方針：正次数元の標準アフィン被覆で斉次局所化の係数写像を比較する。
規約：Mathlib の実際の Proj の射と零次成分の環準同型を用いる。
使われ方：Rees 代数の写像から得る blowup の比較射の基底両立性。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory HomogeneousLocalization

set_option backward.isDefEq.respectTransparency false in
/--
概要：次数付き環準同型が誘導する Proj の射は零次成分上の構造射と両立する。
方針：標準アフィン被覆上で係数の分母一の分数を比較する。
規約：KST §5、Proj の射を定義する irrelevant ideal の包含を仮定する。
使われ方：通常の blowup の係数環に関する比較射。
-/
theorem proj_map_toSpecZero {A B σ τ : Type u}
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro a
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [← Category.assoc, Proj.awayι_comp_map f hf a.1.2 _ a.2.2]
  simp only [Category.assoc, Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp]
  congr 1
  ext x : 2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  apply HomogeneousLocalization.val_injective
  simp [fromZeroRingHom, Away.map, HomogeneousLocalization.map_mk]

set_option backward.isDefEq.respectTransparency false in
/--
概要：像の斉次分母と等しい別表示の分母でも Proj の局所比較公式が成立する。
方針：分母の等式で標的側を移送して、Mathlib の局所公式を適用する。
規約：KST §5、斉次次数は正、分母の所属証明と冪の包含を明示する。
使われ方：Rees 中心元の像に対応する実際の標準チャートの交換式。
-/
@[reassoc] theorem proj_awayι_map_of_eq {A B σ τ : Type u}
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (n : ℕ) (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 n)
    (b : B) (hb : b ∈ ℬ n) (hab : f a = b)
    (hle : Submonoid.powers a ≤ (Submonoid.powers b).comap f.toRingHom) :
    Proj.awayι ℬ b hb hn ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map f hle)) ≫
        Proj.awayι 𝒜 a ha hn := by
  subst b
  exact Proj.awayι_comp_map f hf hn a ha

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
