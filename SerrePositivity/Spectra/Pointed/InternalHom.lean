module

public import SerrePositivity.Spectra.Pointed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# 基点を保つ内部 Hom

## 定義

閉直積圏の内部 Hom から、基点で評価する射と基点で定数となる射の等化子を取る。
基点付き内部 Hom の基点は定数射である。従って各点が基点を保つ写像を表し、
基点自体は零射を表す。

## 仮定と用途

閉構造に加えて等化子の存在を明示する。
行き先に関する関手を構成し、今後 smash の右随伴として使う。
基点付き対象のモノイダル構造を先に仮定せず、基礎圏の閉構造だけを使う。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- 基礎圏の内部 Hom で、基点を値とする定数射を表す点。 -/
def homBasepoint (X Y : PointedObject C) : 𝟙_ C ⟶ (ihom X.right).obj Y.right :=
  curry (toUnit (X.right ⊗ 𝟙_ C) ≫ Y.hom)

/-- 定数射の curry は、定数射を表す点を経由する射となる。 -/
lemma curry_constant {A W Z : C} (p : 𝟙_ C ⟶ Z) :
    curry (toUnit (A ⊗ W) ≫ p) =
      toUnit W ≫ curry (toUnit (A ⊗ 𝟙_ C) ≫ p) := by
  rw [← curry_natural_left]
  congr 1
  simp

/-- 内部 Hom の写像を、定義域の基点へ制限する。 -/
def homRestriction (X Y : PointedObject C) :
    (ihom X.right).obj Y.right ⟶ (ihom (𝟙_ C)).obj Y.right :=
  (pre X.hom).app Y.right

/-- 基点への制限の行き先で、基点を値とする定数射。 -/
def homConstant (X Y : PointedObject C) :
    (ihom X.right).obj Y.right ⟶ (ihom (𝟙_ C)).obj Y.right :=
  toUnit _ ≫ homBasepoint point Y

/-- 定数射を定義域の基点へ制限しても、同じ基点で定数となる。 -/
@[simp] lemma homBasepoint_restriction (X Y : PointedObject C) :
    homBasepoint X Y ≫ homRestriction X Y = homBasepoint point Y := by
  dsimp [homBasepoint, homRestriction, point]
  rw [curry_pre_app]
  congr 1
  simp

variable [HasEqualizers C]

/-- 基点を保つ射の内部 Hom。定数射を表す点は等化子へ持ち上がる。 -/
def basedHom (X Y : PointedObject C) : PointedObject C :=
  Under.mk (equalizer.lift (f := homRestriction X Y) (g := homConstant X Y) (homBasepoint X Y) (by
    simp [homConstant]))

/-- 基点付き内部 Hom から基礎圏の内部 Hom への包含。 -/
def basedHomι (X Y : PointedObject C) : (basedHom X Y).right ⟶ (ihom X.right).obj Y.right :=
  equalizer.ι (homRestriction X Y) (homConstant X Y)

instance basedHomι_mono (X Y : PointedObject C) : Mono (basedHomι X Y) := by
  dsimp [basedHomι]
  infer_instance

@[reassoc (attr := simp)] lemma basedHom_basepoint_ι (X Y : PointedObject C) :
    (basedHom X Y).hom ≫ basedHomι X Y = homBasepoint X Y := equalizer.lift_ι ..

/-- 内部 Hom の包含は、基点への制限が定数射になる条件を満たす。 -/
@[reassoc] lemma basedHomι_condition (X Y : PointedObject C) :
    basedHomι X Y ≫ homRestriction X Y = basedHomι X Y ≫ homConstant X Y :=
  equalizer.condition ..

omit [HasEqualizers C] in
/-- 定数射の点は、基点を保つ行き先の射に関して自然。 -/
@[reassoc (attr := simp)] lemma homBasepoint_map {Y Z : PointedObject C}
    (X : PointedObject C) (f : Y ⟶ Z) :
    homBasepoint X Y ≫ (ihom X.right).map f.right = homBasepoint X Z := by
  rw [homBasepoint, ← curry_natural_right]
  simp [homBasepoint, Category.assoc]

/-- 行き先の射が誘導する、基点付き内部 Hom の射。 -/
def basedHomMap (X : PointedObject C) {Y Z : PointedObject C} (f : Y ⟶ Z) :
    basedHom X Y ⟶ basedHom X Z :=
  Under.homMk (equalizer.lift (f := homRestriction X Z) (g := homConstant X Z)
    (basedHomι X Y ≫ (ihom X.right).map f.right) (by
    have h := basedHomι_condition X Y
    dsimp only [homRestriction] at h ⊢
    rw [Category.assoc, (pre X.hom).naturality f.right, ← Category.assoc, h]
    simp only [homConstant, Category.assoc, comp_toUnit_assoc]
    exact congrArg (fun k ↦ toUnit (basedHom X Y).right ≫ k)
      (homBasepoint_map point f))) (by
      apply (cancel_mono (basedHomι X Z)).mp
      rw [Category.assoc, basedHom_basepoint_ι]
      simp only [basedHomι, equalizer.lift_ι]
      simpa only [Category.assoc, basedHomι] using
        (congrArg (fun k ↦ k ≫ (ihom X.right).map f.right)
          (basedHom_basepoint_ι X Y)).trans (homBasepoint_map X f))

@[reassoc (attr := simp)] lemma basedHomMap_ι (X : PointedObject C)
    {Y Z : PointedObject C} (f : Y ⟶ Z) :
    (basedHomMap X f).right ≫ basedHomι X Z = basedHomι X Y ≫ (ihom X.right).map f.right :=
  equalizer.lift_ι ..

/-- 基点付き内部 Hom は、行き先に関して関手となる。 -/
def basedHomFunctor (X : PointedObject C) : PointedObject C ⥤ PointedObject C where
  obj Y := basedHom X Y
  map f := basedHomMap X f
  map_id Y := by
    apply Under.UnderMorphism.ext
    apply (cancel_mono (basedHomι X Y)).mp
    simp
  map_comp f g := by
    apply Under.UnderMorphism.ext
    apply (cancel_mono (basedHomι X _)).mp
    simp [Category.assoc]

end SerrePositivity.PointedObject
