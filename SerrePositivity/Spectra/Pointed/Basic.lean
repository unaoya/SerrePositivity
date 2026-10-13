module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# 終対象の下の基点付き対象

## 定義

直積をテンソル積とする圏 C について、基点付き対象を終対象からの射の圏として定義する。
対象・射・忘却関手には Mathlib の `Under` を使い、別の圏構造を重複して作らない。
終対象の恒等射が零対象となり、零射は基点を経由する定数射である。

## 用途

単体的集合への特殊化と、一般の基点付き対象の積・smash 積の出発点。
スペクトルやモデル構造を仮定せず、以下の構成は全て証明する。
-/

@[expose] public section

universe v u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

/-- 基点付き対象は、直積モノイダル圏の終対象の下の対象。
基点を保つ射は `Under` の可換三角形であり、既存の圏構造をそのまま使う。 -/
abbrev PointedObject (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] :=
  Under (𝟙_ C)

namespace PointedObject

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- 基点を忘れる関手。射は元の圏の射へ送られる。 -/
abbrev forget : PointedObject C ⥤ C := Under.forget (𝟙_ C)

/-- 終対象に唯一の基点を付けた一つの点。零対象の具体的な代表に使う。 -/
def point : PointedObject C := Under.mk (𝟙 (𝟙_ C))

/-- 一つの点からの射は、対象の基点そのものである。 -/
def fromPoint (X : PointedObject C) : point ⟶ X := Under.homMk X.hom (by simp [point])

/-- 一つの点への射は、基礎圏の終対象への射から得られる。 -/
def toPoint (X : PointedObject C) : X ⟶ point :=
  Under.homMk (toUnit X.right) (by simp [point])

/-- 一つの点は初対象でも終対象でもある。
出る射の一意性は基点を保つ条件、入る射の一意性は基礎圏の終対象の性質による。 -/
lemma point_isZero : IsZero (point : PointedObject C) where
  unique_to X := ⟨{
    default := fromPoint X
    uniq f := by
      apply Under.UnderMorphism.ext
      change f.right = X.hom
      simpa [point] using Under.w f }⟩
  unique_from X := ⟨{
    default := toPoint X
    uniq f := by
      apply Under.UnderMorphism.ext
      exact toUnit_unique _ _ }⟩

/-- 基点付き対象の圏は零対象を持つ。 -/
instance : HasZeroObject (PointedObject C) := ⟨⟨point, point_isZero⟩⟩

/-- 具体的な一つの点から、基点を経由する零射を選ぶ。 -/
noncomputable instance : HasZeroMorphisms (PointedObject C) := point_isZero.hasZeroMorphisms

/-- 一つの点を経由する射は零射。 -/
lemma toPoint_comp_fromPoint (X Y : PointedObject C) : toPoint X ≫ fromPoint Y = 0 := by
  rw [point_isZero.eq_of_tgt (toPoint X) 0, zero_comp]

/-- 零射の基礎圏での表示は、終対象への射と行き先の基点の合成。
後のsmash積の条件を、基点で定数となる条件として読み替えるために使う。 -/
@[simp] lemma zero_right (X Y : PointedObject C) :
    (0 : X ⟶ Y).right = toUnit X.right ≫ Y.hom := by
  rw [← toPoint_comp_fromPoint X Y]
  rfl

end PointedObject
end SerrePositivity
