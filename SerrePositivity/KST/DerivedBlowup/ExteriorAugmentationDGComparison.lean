module

public import SerrePositivity.KST.DerivedBlowup.EmptyKoszulRestriction
public import SerrePositivity.KST.DerivedBlowup.ExteriorAugmentationUniqueness
public import SerrePositivity.KST.DerivedBlowup.ExteriorAugmentationNaturality

/-!
概要：KST Def3.1 の添加 dg 関手の Hom 写像と標準添加鎖写像を同定する。
方針：空 Koszul 比較を合成し、単位保存による添加の一意性を使う。
規約：積・単位保存は既存の dg 関手の合成から得る。
使われ方：標準添加射の擬同型性を添加 dg 関手へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：添加 dg 関手の Hom を単一複体へ同定すると標準添加鎖写像となる。
方針：dg 関手の単位保存と空 Koszul 比較の1保存から一意性を使う。
規約：KST Def3.1。使われ方：添加 dg 関手の局所擬同型性。 -/
theorem exteriorAugmentationDGFunctor_map_comparison (φ : R →+* S)
    (d : M →ₗ[R] R) (hd : ∀ m, φ (d m) = 0) :
    letI := φ.toAlgebra
    (exteriorAugmentationDGFunctor φ d hd).map .point .point ≫
      (emptyKoszulRestrictionIso φ).hom = exteriorKoszulAugmentation d hd := by
  let := φ.toAlgebra
  apply exteriorKoszulAugmentation_unique d hd
  have hu := (exteriorAugmentationDGFunctor φ d hd).map_id ExteriorKoszulObject.point
  change exteriorKoszulUnit d ≫ (exteriorAugmentationDGFunctor φ d hd).map .point .point =
    eId (DifferentialGraded.Complex R)
      (C := DifferentialGraded.ScalarExtension.DGRestriction φ (EmptyKoszulObject S))
      ExteriorKoszulObject.point at hu
  rw [← Category.assoc, hu]
  exact emptyKoszulRestriction_unit_one φ

/-- 概要：標準添加が擬同型なら添加 dg 関手の各 Hom 写像も擬同型。
方針：標準添加との比較と空 Koszul の複体同型で二者三者性を使う。
規約：KST Lemma3.6。使われ方：普遍チャートの dg 準同値。 -/
theorem exteriorAugmentationDGFunctor_map_quasiIso (φ : R →+* S)
    (d : M →ₗ[R] R) (hd : ∀ m, φ (d m) = 0) :
    letI := φ.toAlgebra
    QuasiIso (exteriorKoszulAugmentation d hd) →
      ∀ x y, QuasiIso ((exteriorAugmentationDGFunctor φ d hd).map x y) := by
  let := φ.toAlgebra
  intro h x y
  cases x
  cases y
  have : QuasiIso ((exteriorAugmentationDGFunctor φ d hd).map .point .point ≫
      (emptyKoszulRestrictionIso φ).hom) := by
    rw [exteriorAugmentationDGFunctor_map_comparison]
    exact h
  exact quasiIso_of_comp_right
    ((exteriorAugmentationDGFunctor φ d hd).map .point .point)
    (emptyKoszulRestrictionIso φ).hom

/-- 概要：標準添加が擬同型なら添加 dg 関手は準同値。
方針：各 Hom の擬同型性と一対象型の本質的全射性を組み合わせる。
規約：KST Lemma3.6。使われ方：通常の普遍チャートの局所 dg 模型との比較。 -/
theorem exteriorAugmentationDGFunctor_quasiEquivalence (φ : R →+* S)
    (d : M →ₗ[R] R) (hd : ∀ m, φ (d m) = 0) :
    letI := φ.toAlgebra
    QuasiIso (exteriorKoszulAugmentation d hd) →
      DifferentialGraded.QuasiEquivalence (exteriorAugmentationDGFunctor φ d hd) := by
  let := φ.toAlgebra
  intro h
  constructor
  · exact exteriorAugmentationDGFunctor_map_quasiIso φ d hd h
  · apply Functor.essSurj_of_surj
    rintro ⟨y⟩
    change EmptyKoszulObject S at y
    cases y
    exact ⟨⟨ExteriorKoszulObject.point⟩, rfl⟩

end SerrePositivity.KST.DerivedBlowup
