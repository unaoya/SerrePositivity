module

public import SerrePositivity.Spectra.Pointed.SmashCurrying
public import SerrePositivity.Spectra.Pointed.SmashSymmetry

/-!
# smash 積と基点付き内部 Hom の随伴

Hom 同値の二つの変数に関する自然性を証明して、随伴へまとめる。
従って各対象との smash は左随伴であり、余極限を保存する。
この保存結果は、今後の結合子・対称列・モデル圏への接続で再利用できる。
smash のモノイダル構造を先に仮定せず、基礎圏の閉構造と等化子から証明する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasFiniteColimits C]

/-- smash の curry は、第二変数の引き戻しと両立する。 -/
lemma smashCurry_natural_left {X Y Y' Z : PointedObject C} (f : Y ⟶ Y')
    (g : smash X Y' ⟶ Z) : smashCurry (smashMap (𝟙 X) f ≫ g) = f ≫ smashCurry g := by
  apply Under.UnderMorphism.ext
  apply (cancel_mono (basedHomι X Z)).mp
  simp only [Under.comp_right, Category.assoc, smashCurry_ι]
  have h := congrArg Under.Hom.right (smashQuotient_map (𝟙 X) f)
  simp only [Under.comp_right, prodMap_right, Under.id_right, id_tensorHom] at h
  rw [← Category.assoc, h, Category.assoc, curry_natural_left]

/-- smash の curry は、行き先への写像と両立する。 -/
lemma smashCurry_natural_right {X Y Z Z' : PointedObject C} (f : smash X Y ⟶ Z)
    (g : Z ⟶ Z') : smashCurry (f ≫ g) = smashCurry f ≫ basedHomMap X g := by
  apply Under.UnderMorphism.ext
  apply (cancel_mono (basedHomι X Z')).mp
  simp only [Under.comp_right, Category.assoc, basedHomMap_ι, smashCurry_ι,
    smashCurry_ι_assoc]
  rw [← Category.assoc, curry_natural_right]

@[simp] lemma smashCurry_symm {X Y Z : PointedObject C} (f : Y ⟶ basedHom X Z) :
    smashCurry ((smashBasedHomEquiv X Y Z).symm f) = f :=
  (smashBasedHomEquiv X Y Z).apply_symm_apply f

/-- 各対象との smash は、基点付き内部 Hom を右随伴に持つ。
商の普遍性と curry の Hom 同値の自然性から構成する。 -/
def smashHomAdjunction (X : PointedObject C) :
    (smashFunctor (C := C)).obj X ⊣ basedHomFunctor X :=
  Adjunction.mkOfHomEquiv {
    homEquiv := smashBasedHomEquiv X
    homEquiv_naturality_left_symm := fun f g ↦ by
      apply (smashBasedHomEquiv X _ _).injective
      change smashCurry ((smashBasedHomEquiv X _ _).symm (f ≫ g)) =
        smashCurry (smashMap (𝟙 X) f ≫ (smashBasedHomEquiv X _ _).symm g)
      simp only [smashCurry_symm, smashCurry_natural_left]
    homEquiv_naturality_right := fun f g ↦ smashCurry_natural_right f g }

/-- 基点付き内部 Hom の評価射。構成した随伴の余単位を使う。 -/
def smashEvaluation (X Y : PointedObject C) : smash X (basedHom X Y) ⟶ Y :=
  (smashHomAdjunction X).counit.app Y

/-- 基点付き内部 Hom の余評価射。構成した随伴の単位を使う。 -/
def smashCoevaluation (X Y : PointedObject C) : Y ⟶ basedHom X (smash X Y) :=
  (smashHomAdjunction X).unit.app Y

/-- smash 側での評価・余評価の三角恒等式。 -/
@[reassoc (attr := simp)] lemma smashEvaluation_coevaluation (X Y : PointedObject C) :
    smashMap (𝟙 X) (smashCoevaluation X Y) ≫ smashEvaluation X (smash X Y) =
      𝟙 (smash X Y) := (smashHomAdjunction X).left_triangle_components Y

/-- 内部 Hom 側での評価・余評価の三角恒等式。 -/
@[reassoc (attr := simp)] lemma basedHomEvaluation_coevaluation (X Y : PointedObject C) :
    smashCoevaluation X (basedHom X Y) ≫ basedHomMap X (smashEvaluation X Y) =
      𝟙 (basedHom X Y) := (smashHomAdjunction X).right_triangle_components Y

instance smashLeft_isLeftAdjoint (X : PointedObject C) :
    ((smashFunctor (C := C)).obj X).IsLeftAdjoint := (smashHomAdjunction X).isLeftAdjoint

instance basedHom_isRightAdjoint (X : PointedObject C) :
    (basedHomFunctor X).IsRightAdjoint := (smashHomAdjunction X).isRightAdjoint

/-- 左からの smash は余極限を保存する。 -/
instance smashLeft_preservesColimits (X : PointedObject C) :
    PreservesColimits ((smashFunctor (C := C)).obj X) :=
  (smashHomAdjunction X).leftAdjoint_preservesColimits

/-- 左右の smash 関手は、交換同型によって自然同型になる。 -/
def smashRightLeftIso (X : PointedObject C) :
    (smashFunctor (C := C)).flip.obj X ≅ (smashFunctor (C := C)).obj X :=
  NatIso.ofComponents (fun Y ↦ smashSymmetry Y X) (by
    intro Y Z f
    exact smashSwap_naturality f (𝟙 X))

instance smashRight_isLeftAdjoint (X : PointedObject C) :
    ((smashFunctor (C := C)).flip.obj X).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (smashRightLeftIso X).symm

/-- 右からの smash も余極限を保存する。 -/
instance smashRight_preservesColimits (X : PointedObject C) :
    PreservesColimits ((smashFunctor (C := C)).flip.obj X) :=
  inferInstance

end SerrePositivity.PointedObject
