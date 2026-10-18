module
public import SerrePositivity.KST.SConstruction.DiagonalReduction

/-! # 二重単体集合の object 単体集合から対角への射
概要：内部の零単体を退化させ、各行の object から対角への自然な射を作る。
方針：零次数への唯一の射による退化と自然性を使う。
規約：弱同値性は主張しない。使われ方：McCarthy 法の object/core 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：二重単体集合の各行の零単体からなる単体集合。
方針：内部の零次数で評価する。
規約：内部の高次単体をまだ使わない。使われ方：S• の object 単体集合。 -/
def diagonalObjects (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u} :=
  X ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)

/-- 概要：各行の object を内部の退化で対角へ送る。
方針：内部の零次数から対角次数への定数退化を使う。
規約：全高次の外部単体も保持する。使われ方：object/core 実現比較の実際の射。 -/
def diagonalObjectInclusion (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalObjects X ⟶ simplicialDiagonalFunctor.obj X where
  app d := (X.obj d).map (SimplexCategory.const d.unop ⦋0⦌ 0).op
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro x
    have hn := ConcreteCategory.congr_hom
      ((X.map f).naturality (SimplexCategory.const d.unop ⦋0⦌ 0).op) x
    change (X.map f).app d ((X.obj d).map (SimplexCategory.const d.unop ⦋0⦌ 0).op x) =
      (X.obj e).map (SimplexCategory.const d.unop ⦋0⦌ 0).op
        ((X.map f).app (Opposite.op ⦋0⦌) x) at hn
    change (X.obj e).map (SimplexCategory.const e.unop ⦋0⦌ 0).op
        ((X.map f).app (Opposite.op ⦋0⦌) x) =
      (X.obj e).map f
        ((X.map f).app d ((X.obj d).map (SimplexCategory.const d.unop ⦋0⦌ 0).op x))
    rw [hn]
    change _ = ((X.obj e).map (SimplexCategory.const d.unop ⦋0⦌ 0).op ≫ (X.obj e).map f) _
    rw [← CategoryTheory.Functor.map_comp]
    have hc : (SimplexCategory.const d.unop ⦋0⦌ 0).op ≫ f =
        (SimplexCategory.const e.unop ⦋0⦌ 0).op := by
      apply Quiver.Hom.unop_inj
      exact Subsingleton.elim _ _
    rw [hc]

/-- 概要：object の対角への射は二重単体集合について自然。
方針：内部の定数退化についての自然性を使う。
規約：厳密な自然変換。使われ方：object/core 比較の入力の自然性。 -/
def diagonalObjectInclusionNat :
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) ⟶
      simplicialDiagonalFunctor where
  app := diagonalObjectInclusion
  naturality {_X _Y} f := by
    apply NatTrans.ext
    funext d
    exact ((f.app d).naturality (SimplexCategory.const d.unop ⦋0⦌ 0).op).symm

end SerrePositivity.KST.SConstruction
