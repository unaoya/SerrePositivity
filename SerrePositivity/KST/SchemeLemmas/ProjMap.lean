module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
概要：KST §5 の比較に必要な Proj の構造射の自然性。
方針：正次数元の標準アフィン被覆で斉次局所化の係数写像を比較する。
規約：Mathlib の実際の Proj の射と零次成分の環準同型を用いる。
使われ方：Rees 代数の写像から得る blowup の比較射の基底両立性。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.KST.SchemeLemmas
open AlgebraicGeometry CategoryTheory HomogeneousLocalization

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

end SerrePositivity.KST.SchemeLemmas
