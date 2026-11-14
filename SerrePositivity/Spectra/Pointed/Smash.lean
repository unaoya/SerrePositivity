module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.Spectra.Pointed.Products
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# 基点付き対象の smash 積

## 定義と仮定

基礎圏が直積と有限余極限を持つとき、基点付き対象の wedge は under 圏の二項余積。
二つの軸から wedge → product を作り、その wedge を一つの点へ潰す pushout を smash と定義する。
この一般性では、smash が結合的・閉対称モノイダルであることはまだ主張しない。

## 普遍性

smash から出る射は、直積から出る基点付き射で両方の軸を零にするものと対応する。
この普遍性から射の写像、恒等射・合成の保存と二変数の関手を構成する。
モデル構造やホモトピー不変性を仮定せず、全て通常の圏の構成として証明する。
-/

@[expose] public section

universe v u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasFiniteColimits C]

/-- 基点付き対象の wedge。基点を同一視する二項余積を使う。 -/
noncomputable abbrev wedge (X Y : PointedObject C) : PointedObject C := X ⨿ Y

/-- 二つの軸が誘導する wedge から直積への射。 -/
noncomputable def wedgeToProd (X Y : PointedObject C) : wedge X Y ⟶ prod X Y :=
  coprod.desc (axisLeft X Y) (axisRight X Y)

/-- 直積の二つの軸を基点へ潰した smash 積。通常の pushout による定義。 -/
noncomputable def smash (X Y : PointedObject C) : PointedObject C :=
  pushout (wedgeToProd X Y) (toPoint (wedge X Y))

/-- 直積から smash 積への標準の射。 -/
noncomputable def smashQuotient (X Y : PointedObject C) : prod X Y ⟶ smash X Y :=
  pushout.inl _ _

/-- wedge の像は smash 積では零となる。 -/
@[reassoc (attr := simp)] lemma wedgeToProd_smashQuotient (X Y : PointedObject C) :
    wedgeToProd X Y ≫ smashQuotient X Y = 0 := by
  change wedgeToProd X Y ≫ pushout.inl _ _ = 0
  rw [pushout.condition, point_isZero.eq_of_src (pushout.inr _ _) 0, comp_zero]

/-- smash 積では第一の軸が零になる。 -/
@[reassoc (attr := simp)] lemma axisLeft_smashQuotient (X Y : PointedObject C) :
    axisLeft X Y ≫ smashQuotient X Y = 0 := by
  have h := congrArg (fun f ↦ (coprod.inl : X ⟶ wedge X Y) ≫ f)
    (wedgeToProd_smashQuotient X Y)
  simpa [wedgeToProd, Category.assoc] using h

/-- smash 積では第二の軸が零になる。 -/
@[reassoc (attr := simp)] lemma axisRight_smashQuotient (X Y : PointedObject C) :
    axisRight X Y ≫ smashQuotient X Y = 0 := by
  have h := congrArg (fun f ↦ (coprod.inr : Y ⟶ wedge X Y) ≫ f)
    (wedgeToProd_smashQuotient X Y)
  simpa [wedgeToProd, Category.assoc] using h

/-- 両方の軸を零にする直積上の射は、smash 積からの射へ降りる。
pushout の普遍性を使い、一つの点からの射には零射を選ぶ。 -/
noncomputable def smashDesc {X Y Z : PointedObject C} (f : prod X Y ⟶ Z)
    (h₁ : axisLeft X Y ≫ f = 0) (h₂ : axisRight X Y ≫ f = 0) : smash X Y ⟶ Z :=
  pushout.desc f 0 (by
    apply coprod.hom_ext <;> simp [wedgeToProd, h₁, h₂])

/-- 降ろした射を直積へ引き戻すと元の射になる。 -/
@[reassoc (attr := simp)] lemma smashQuotient_desc {X Y Z : PointedObject C}
    (f : prod X Y ⟶ Z) (h₁) (h₂) : smashQuotient X Y ≫ smashDesc f h₁ h₂ = f :=
  pushout.inl_desc ..

/-- smash 積から出る射は、直積からの標準射との合成で決まる。
pushout の他方の脚は零対象から出るため、その合成は自動的に一致する。 -/
@[ext] lemma smash_hom_ext {X Y Z : PointedObject C} (f g : smash X Y ⟶ Z)
    (h : smashQuotient X Y ≫ f = smashQuotient X Y ≫ g) : f = g := by
  apply pushout.hom_ext
  · exact h
  · exact point_isZero.eq_of_src _ _

/-- 直積から smash 積への標準射はエピ射。普遍性による零化の判定に用いる。 -/
instance smashQuotient_epi (X Y : PointedObject C) : Epi (smashQuotient X Y) where
  left_cancellation _ _ h := smash_hom_ext _ _ h

/-- smash 積の普遍性を Hom 集合の同値として表す。
結合性や単位の今後の比較も、この軸の零化条件に帰着できる。 -/
noncomputable def smashHomEquiv (X Y Z : PointedObject C) :
    (smash X Y ⟶ Z) ≃
      {f : prod X Y ⟶ Z // axisLeft X Y ≫ f = 0 ∧ axisRight X Y ≫ f = 0} where
  toFun f := ⟨smashQuotient X Y ≫ f, by simp, by simp⟩
  invFun f := smashDesc f.1 f.2.1 f.2.2
  left_inv f := smash_hom_ext _ _ (by simp)
  right_inv f := Subtype.ext (by simp)

/-- 二つの基点付き射が smash 積に誘導する射。軸の自然性と零化から定義する。 -/
noncomputable def smashMap {X Y X' Y' : PointedObject C} (f : X ⟶ X') (g : Y ⟶ Y') :
    smash X Y ⟶ smash X' Y' :=
  smashDesc (prodMap f g ≫ smashQuotient X' Y') (by simp) (by simp)

/-- smash 積上の写像は直積の写像と両立する。 -/
@[reassoc (attr := simp)] lemma smashQuotient_map {X Y X' Y' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    smashQuotient X Y ≫ smashMap f g = prodMap f g ≫ smashQuotient X' Y' :=
  smashQuotient_desc ..

/-- smash 積の写像は恒等射を保つ。 -/
@[simp] lemma smashMap_id (X Y : PointedObject C) :
    smashMap (𝟙 X) (𝟙 Y) = 𝟙 (smash X Y) := by
  apply smash_hom_ext
  simp

/-- smash 積の写像は合成を保つ。 -/
@[simp] lemma smashMap_comp {X Y X' Y' X'' Y'' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') (f' : X' ⟶ X'') (g' : Y' ⟶ Y'') :
    smashMap f g ≫ smashMap f' g' = smashMap (f ≫ f') (g ≫ g') := by
  apply smash_hom_ext
  simp [Category.assoc, ← prodMap_comp]

/-- 通常の smash 積の二変数関手。
ホモトピー論の導来 smash とは区別し、後でその基礎となる関手として使う。 -/
noncomputable def smashFunctor : PointedObject C ⥤ PointedObject C ⥤ PointedObject C where
  obj X := {
    obj Y := smash X Y
    map g := smashMap (𝟙 X) g
    map_id Y := smashMap_id X Y
    map_comp g h := by simp }
  map f := {
    app Y := smashMap f (𝟙 Y)
    naturality g := by simp }
  map_id X := by
    apply NatTrans.ext
    funext Y
    exact smashMap_id X Y
  map_comp f g := by
    apply NatTrans.ext
    funext Y
    simp

end SerrePositivity.PointedObject

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.2.5.1" (partial := component) "仮定：有限積・有限余極限を持つ圏の基点付き対象（Lean は Type の有限対象以外にも適用できる）。結論：積のうちいずれかの座標が基点となる部分を潰す smash の二関手（HA の基点付き集合上の構成に一致）。標準有限集合上の辞書式番号づけは型に含まれない。"] _root_.SerrePositivity.PointedObject.smashFunctor
