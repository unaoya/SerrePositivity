module
public import SerrePositivity.KST.SConstruction.DiagonalObjects

/-! # object の各行への包含と転置した対角
概要：二重単体集合の object 単体集合を転置後の各行へ自然に含める。
方針：内部次数零からの退化を全次数で使い、対角の転置を恒等成分で同定する。
規約：弱同値性は別に示す。使われ方：object/core 比較の行から対角への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：object 単体集合を転置した二重単体集合の指定行に含める。
方針：内部の零単体を指定次数に退化させる。
規約：任意の二重単体集合。使われ方：各行の弱同値性の照合。 -/
def objectRowInclusion (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    diagonalObjects X ⟶ X.flip.obj m where
  app n := (X.obj n).map (SimplexCategory.const m.unop ⦋0⦌ 0).op
  naturality {_n _l} θ := ((X.map θ).naturality
    (SimplexCategory.const m.unop ⦋0⦌ 0).op).symm

/-- 概要：object から各行への包含は行の次数について自然。
方針：退化と任意の単体作用素の合成が同じ定値写像であることを使う。
規約：源は object 単体集合の定数図式。使われ方：対角の局所化比較。 -/
def objectRowsInclusion (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj (diagonalObjects X) ⟶ X.flip where
  app := objectRowInclusion X
  naturality {m l} θ := by
    apply NatTrans.ext
    funext n
    change 𝟙 _ ≫ _ = (X.obj n).map (SimplexCategory.const m.unop ⦋0⦌ 0).op ≫
      (X.obj n).map θ
    rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
    congr 1

/-- 概要：二重単体集合の対角は転置前後で同型。
方針：各次数では恒等写像を使い、自然性は二方向の可換性から得る。
規約：対角の構造射の順序の違いを隠さない。使われ方：元の比較射との照合。 -/
def diagonalFlipIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    simplicialDiagonalFunctor.obj X.flip ≅ simplicialDiagonalFunctor.obj X :=
  NatIso.ofComponents (fun n => Iso.refl _) (by
    intro n l θ
    change ((X.obj n).map θ ≫ (X.map θ).app l) ≫ 𝟙 _ =
      𝟙 _ ≫ ((X.map θ).app n ≫ (X.obj l).map θ)
    simp only [Category.comp_id, Category.id_comp]
    exact (X.map θ).naturality θ)

/-- 概要：定数な行の二重単体集合の対角は元の単体集合と同型。
方針：各次数で恒等写像を使う。
規約：対角の定数な方向だけを忘れる。使われ方：対角比較の源の同定。 -/
def diagonalConstIso (A : SSet.{u}) :
    A ≅ simplicialDiagonalFunctor.obj ((Functor.const SimplexCategoryᵒᵖ).obj A) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n l θ
    rfl)

/-- 概要：各行の object 包含の対角は元の object から対角への射。
方針：各次数の同じ零次元からの退化を照合する。
規約：源と標的の同定を明示する。使われ方：行の弱同値から元の比較の弱同値を得る。 -/
lemma objectRowsInclusion_diagonal (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (diagonalConstIso (diagonalObjects X)).hom ≫
      simplicialDiagonalFunctor.map (objectRowsInclusion X) ≫ (diagonalFlipIso X).hom =
      diagonalObjectInclusion X := by
  apply NatTrans.ext
  funext n
  rfl

end SerrePositivity.KST.SConstruction
