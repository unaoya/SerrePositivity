module
public import SerrePositivity.KST.SConstruction.RawCofiberTensorEvaluation
public import SerrePositivity.KST.SConstruction.CofiberTensorExt
public import SerrePositivity.KST.Spectra.CofiberMappingFamilies

/-! # 二つの cofiber の smash の全写像族の検出
概要：全パラメータを持つ基点固定写像族を、元の二つの対象の直積上で検出する。
方針：自由基点付き直積からのエピ射と、非基点成分・基点成分の二脚を使う。
規約：境界の非空性を仮定しない。使われ方：元の suspension の全族自然性の降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open Spectra

/-- 元の直積に自由基点を加えた対象から、二つの cofiber の smash への標準の射。 -/
def cofiberTensorCover {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    PointedObject.adjoin (B ⊗ D) ⟶ PointedObject.cofiber f ⊗ PointedObject.cofiber g :=
  PointedObject.adjoinSmashInv B D ≫
    (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g)

/-- 自由基点付き直積からの標準の射は、境界の非空性なしでエピ。 -/
instance cofiberTensorCover_epi {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    Epi (cofiberTensorCover f g) := by
  change Epi ((PointedObject.adjoinSmashIso B D).inv ≫
    (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g))
  infer_instance

/-- 元の非基点成分では、二つの元の商射を smash 商へ送る射になる。 -/
lemma cofiberTensorCover_inl {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    coprod.inl ≫ (cofiberTensorCover f g).right =
      (PointedObject.cofiberQuotient f ⊗ₘ PointedObject.cofiberQuotient g) ≫
        PointedSimplicialSet.productToSmash (PointedObject.cofiber f)
          (PointedObject.cofiber g) := by
  change coprod.inl ≫ (PointedObject.adjoinSmashInv B D).right ≫
    (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g).right = _
  erw [← Category.assoc, PointedObject.adjoinSmashInv_first, Category.assoc,
    ← PointedSimplicialSet.productToSmash_naturality, ← Category.assoc,
    tensorHom_comp_tensorHom, PointedObject.cofiberProjection_underlying,
    PointedObject.cofiberProjection_underlying]

/-- 二つの元の商射に沿う評価は、smash からの基点固定写像族を一意に決める。 -/
lemma cofiberTensorFamily_hom_ext {A B C D P : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u})
    {a b : P ⟶ (PointedObject.basedHom
      (PointedObject.cofiber f ⊗ PointedObject.cofiber g) Z).right}
    (h : (((PointedObject.cofiberQuotient f ⊗ₘ PointedObject.cofiberQuotient g) ≫
        PointedSimplicialSet.productToSmash (PointedObject.cofiber f)
          (PointedObject.cofiber g)) ▷ P) ≫
        uncurry (a ≫ PointedObject.basedHomι _ Z) =
      (((PointedObject.cofiberQuotient f ⊗ₘ PointedObject.cofiberQuotient g) ≫
        PointedSimplicialSet.productToSmash (PointedObject.cofiber f)
          (PointedObject.cofiber g)) ▷ P) ≫
        uncurry (b ≫ PointedObject.basedHomι _ Z)) : a = b := by
  apply (cancel_mono (PointedObject.basedHomι _ Z)).mp
  apply uncurry_injective
  have : Epi ((cofiberTensorCover f g).right ▷ P) :=
    (tensorRight P).map_epi (cofiberTensorCover f g).right
  apply (cancel_epi ((cofiberTensorCover f g).right ▷ P)).mp
  apply PointedObject.tensorRightCoprod_hom_ext
  · erw [← comp_whiskerRight_assoc, cofiberTensorCover_inl,
      ← comp_whiskerRight_assoc, cofiberTensorCover_inl]
    exact h
  · have hw := Under.w (cofiberTensorCover f g)
    change coprod.inr ≫ (cofiberTensorCover f g).right =
      (PointedObject.cofiber f ⊗ PointedObject.cofiber g).hom at hw
    erw [← comp_whiskerRight_assoc, hw, ← comp_whiskerRight_assoc, hw,
      basedHomFamily_basepoint, basedHomFamily_basepoint]

end SerrePositivity.KST.SConstruction
