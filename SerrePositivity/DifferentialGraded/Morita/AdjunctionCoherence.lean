module
public import SerrePositivity.DifferentialGraded.Morita.U16a
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 恒等・合成kernelの実際の右随伴の比較

## 概要
一般右随伴を恒等kernelと合成kernelで計算し、実際のunit/counitの比較を公開する。

## 方針
既存kernelIdentityIso・kernelCompositionIsoで随伴を移し、右随伴の一意性を適用する。

## 規約と注意
kernelのMorita性・列の射影性は不要。合成には始域DのlocalHomKFlatだけを保持する。

## 使われ方
U16の実際の一般右随伴による恒等・逆順合成の計算と、Morita逆関手の合成比較。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 恒等作用の実際の比較から作った、恒等関手を右随伴とする随伴。 -/
def kernelIdentityRightAdjunction :
    kernelDerivedTensor A D D (kernelIdentity A D) ⊣ 𝟭 (DerivedModuleCategory A D) :=
  Adjunction.id.ofNatIsoLeft (kernelIdentityIso A D).symm

/-- 恒等kernelの実際の一般右随伴は恒等関手に自然同型。 -/
def kernelDerivedHomIdentityIso :
    kernelDerivedHom A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D) :=
  Adjunction.rightAdjointUniq (kernelDerivedAdjunction A D D (kernelIdentity A D))
    (kernelIdentityRightAdjunction A D)

/-- 恒等kernelの右随伴比較は、実際の単位と恒等作用比較を接続する。 -/
lemma kernelDerivedHomIdentityIso_unit (X : DerivedModuleCategory A D) :
    (kernelDerivedUnit A D D (kernelIdentity A D)).app X ≫
      (kernelDerivedHomIdentityIso A D).hom.app
        ((kernelDerivedTensor A D D (kernelIdentity A D)).obj X) =
    (kernelIdentityIso A D).inv.app X := by
  have h := Adjunction.unit_rightAdjointUniq_hom_app
    (kernelDerivedAdjunction A D D (kernelIdentity A D)) (kernelIdentityRightAdjunction A D) X
  change _ = 𝟙 _ ≫ (𝟭 (DerivedModuleCategory A D)).map ((kernelIdentityIso A D).inv.app X) at h
  simpa only [Functor.id_map, Functor.id_obj, Category.id_comp, kernelDerivedUnit,
    kernelDerivedHomIdentityIso] using h

/-- 恒等kernelの右随伴比較は、実際の余単位と恒等作用比較を接続する。 -/
lemma kernelDerivedHomIdentityIso_counit (Y : DerivedModuleCategory A D) :
    (kernelDerivedTensor A D D (kernelIdentity A D)).map
        ((kernelDerivedHomIdentityIso A D).hom.app Y) ≫
      (kernelIdentityIso A D).hom.app Y =
    (kernelDerivedCounit A D D (kernelIdentity A D)).app Y := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (kernelDerivedAdjunction A D D (kernelIdentity A D)) (kernelIdentityRightAdjunction A D) Y
  change _ ≫ ((kernelIdentityIso A D).hom.app Y ≫ 𝟙 _) = _ at h
  simpa only [Category.comp_id, kernelDerivedCounit, kernelDerivedHomIdentityIso] using h

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E F)

/-- 合成kernel作用に、二つの実際の一般右随伴の逆順合成を随伴させる。 -/
def kernelCompositionRightAdjunction :
    kernelDerivedTensor A D F (kernelCompose A D E F hD P Q) ⊣
      kernelDerivedHom A E F Q ⋙ kernelDerivedHom A D E P :=
  ((kernelDerivedAdjunction A D E P).comp (kernelDerivedAdjunction A E F Q)).ofNatIsoLeft
    (kernelCompositionIso A D E F hD P Q)

/-- 移した合成随伴の単位は元の二つの実際の単位で計算する。 -/
lemma kernelCompositionRightAdjunction_unit_app (X : DerivedModuleCategory A D) :
    (kernelCompositionRightAdjunction A D E F hD P Q).unit.app X =
      (kernelDerivedUnit A D E P).app X ≫
        (kernelDerivedHom A D E P).map
          ((kernelDerivedUnit A E F Q).app ((kernelDerivedTensor A D E P).obj X)) ≫
        (kernelDerivedHom A D E P).map
          ((kernelDerivedHom A E F Q).map ((kernelCompositionIso A D E F hD P Q).hom.app X)) := by
  change ((kernelDerivedAdjunction A D E P).comp (kernelDerivedAdjunction A E F Q)).unit.app X ≫
    (kernelDerivedHom A D E P).map
      ((kernelDerivedHom A E F Q).map ((kernelCompositionIso A D E F hD P Q).hom.app X)) = _
  rw [Adjunction.comp_unit_app]
  simp only [kernelDerivedUnit, Category.assoc]

/-- 移した合成随伴の余単位は元の二つの実際の余単位で計算する。 -/
lemma kernelCompositionRightAdjunction_counit_app (Y : DerivedModuleCategory A F) :
    (kernelCompositionRightAdjunction A D E F hD P Q).counit.app Y =
      (kernelCompositionIso A D E F hD P Q).inv.app
          ((kernelDerivedHom A D E P).obj ((kernelDerivedHom A E F Q).obj Y)) ≫
        (kernelDerivedTensor A E F Q).map
          ((kernelDerivedCounit A D E P).app ((kernelDerivedHom A E F Q).obj Y)) ≫
        (kernelDerivedCounit A E F Q).app Y := by
  change (kernelCompositionIso A D E F hD P Q).inv.app _ ≫
    ((kernelDerivedAdjunction A D E P).comp (kernelDerivedAdjunction A E F Q)).counit.app Y = _
  rw [Adjunction.comp_counit_app]
  rfl

/-- 合成kernelの実際の一般右随伴は、二つの一般右随伴の逆順合成に自然同型。 -/
def kernelDerivedHomCompositionIso :
    kernelDerivedHom A D F (kernelCompose A D E F hD P Q) ≅
      kernelDerivedHom A E F Q ⋙ kernelDerivedHom A D E P :=
  Adjunction.rightAdjointUniq
    (kernelDerivedAdjunction A D F (kernelCompose A D E F hD P Q))
    (kernelCompositionRightAdjunction A D E F hD P Q)

/-- 合成kernelの右随伴比較は、元の二つの実際の単位との図式を満たす。 -/
lemma kernelDerivedHomCompositionIso_unit (X : DerivedModuleCategory A D) :
    (kernelDerivedUnit A D F (kernelCompose A D E F hD P Q)).app X ≫
      (kernelDerivedHomCompositionIso A D E F hD P Q).hom.app
        ((kernelDerivedTensor A D F (kernelCompose A D E F hD P Q)).obj X) =
    (kernelDerivedUnit A D E P).app X ≫
      (kernelDerivedHom A D E P).map
        ((kernelDerivedUnit A E F Q).app ((kernelDerivedTensor A D E P).obj X)) ≫
      (kernelDerivedHom A D E P).map
        ((kernelDerivedHom A E F Q).map ((kernelCompositionIso A D E F hD P Q).hom.app X)) :=
  (Adjunction.unit_rightAdjointUniq_hom_app
    (kernelDerivedAdjunction A D F (kernelCompose A D E F hD P Q))
    (kernelCompositionRightAdjunction A D E F hD P Q) X).trans
      (kernelCompositionRightAdjunction_unit_app A D E F hD P Q X)

/-- 合成kernelの右随伴比較は、元の二つの実際の余単位との図式を満たす。 -/
lemma kernelDerivedHomCompositionIso_counit (Y : DerivedModuleCategory A F) :
    (kernelDerivedTensor A D F (kernelCompose A D E F hD P Q)).map
        ((kernelDerivedHomCompositionIso A D E F hD P Q).hom.app Y) ≫
      (kernelCompositionIso A D E F hD P Q).inv.app
          ((kernelDerivedHom A D E P).obj ((kernelDerivedHom A E F Q).obj Y)) ≫
      (kernelDerivedTensor A E F Q).map
        ((kernelDerivedCounit A D E P).app ((kernelDerivedHom A E F Q).obj Y)) ≫
      (kernelDerivedCounit A E F Q).app Y =
    (kernelDerivedCounit A D F (kernelCompose A D E F hD P Q)).app Y := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (kernelDerivedAdjunction A D F (kernelCompose A D E F hD P Q))
    (kernelCompositionRightAdjunction A D E F hD P Q) Y
  rw [kernelCompositionRightAdjunction_counit_app] at h
  exact h

end SerrePositivity.DifferentialGraded.Morita
