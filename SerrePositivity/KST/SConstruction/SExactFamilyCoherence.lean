module
public import SerrePositivity.KST.SConstruction.SExactFamilyAction

/-! # 全完全関手族に対する S_n 作用の厳密 coherence
概要：全パラメータの S_n 作用は、恒等・合成と全ての面退化を厳密に保つ。
方針：元の図式空間への包含後に、内部 Hom の実合成と添字制限を照合する。
規約：頂点だけの可換性ではない。使われ方：厳密豊穣 S• と反復 S•。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 全完全関手族の恒等入力は、元の S_n の恒等作用を与える。 -/
lemma sExactFamilyAction_unit (n : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (𝟙 (sConstruction n C.obj) ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity C) ≫ sExactFamilyAction n C C =
      (ρ_ (sConstruction n C.obj)).hom := by
  have hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv (𝟙 C) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity C := eHomEquiv_id SSet C
  have h := sExactFamilyAction_fixed n (𝟙 C)
  erw [hp, sPostcompCofiber_id, Category.comp_id] at h
  exact h

/-- 全完全関手族の二回の作用は、同じ入力合成による作用に厳密に一致する。 -/
lemma sExactFamilyAction_comp (n : ℕ) (C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (sExactFamilyAction n C D ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors D E : SSet.{u})) ≫
        sExactFamilyAction n D E =
      (α_ (sConstruction n C.obj) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors D E : SSet.{u})).hom ≫
          (𝟙 (sConstruction n C.obj) ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition C D E) ≫ sExactFamilyAction n C E := by
  ext k p
  apply Subtype.ext
  apply Functor.functorHom_ext
  intro m f
  apply ConcreteCategory.hom_ext
  intro q
  rfl

/-- 元の全パラメータ作用は、全ての面退化による添字制限と厳密に可換する。 -/
lemma sExactFamilyAction_sMap {m n : ℕ} (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    sExactFamilyAction n C D ≫ sMap D.obj θ =
      (sMap C.obj θ ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})) ≫ sExactFamilyAction m C D := by
  ext k p
  apply Subtype.ext
  apply Functor.functorHom_ext
  intro l f
  apply ConcreteCategory.hom_ext
  intro q
  rfl

end SerrePositivity.KST.SConstruction
