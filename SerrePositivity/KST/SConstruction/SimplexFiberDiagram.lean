module
public import SerrePositivity.KST.SConstruction.SimplexLeftFiber
public import Mathlib.CategoryTheory.Elements

/-! # 単体圏上の strict 左 fiber の図式
概要：Y の各単体上の f:X→Y の左 fiber を単体圏の反対圏上の共変図式にする。
方針：単体の射でパラメーターを後合成し、元の X の単体は保持する。
規約：単体のラベルの等号を輸送で隠さず pullback の可換性で処理する。使われ方：単体積版 Quillen A。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：単体圏の射は strict 左 fiber の間の射を与える。
方針：元の図式の射影を保ち、標準単体パラメーターに単体の射を後合成する。
規約：元の単体のラベルの等号を明示する。使われ方：左 fiber 図式の射。 -/
def simplexFiberDiagramMap {X Y : SSet.{u}} (f : X ⟶ Y) {a b : Y.Elementsᵒᵖ} (h : a ⟶ b) :
    simplexLeftFiber f a.unop.val ⟶ simplexLeftFiber f b.unop.val :=
  simplexLeftFiberLift f b.unop.val (simplexLeftFiberProjection f a.unop.val)
    (simplexLeftFiberParameter f a.unop.val ≫ stdSimplex.map h.unop.hom.unop) (by
      rw [simplexLeftFiber_condition, Category.assoc]
      congr 1
      have hy : Y.map h.unop.hom b.unop.val = a.unop.val := h.unop.map_val
      rw [← hy]
      exact (SSet.yonedaEquiv_symm_naturality_left h.unop.hom.unop b.unop.val).symm)

/-- 概要：単体圏の射による左 fiber の射は元の X の単体を保持する。
方針：pullback の第一射影の式。
規約：全単体での等号。使われ方：quotient への射の自然性。 -/
lemma simplexFiberDiagramMap_projection {X Y : SSet.{u}} (f : X ⟶ Y)
    {a b : Y.Elementsᵒᵖ} (h : a ⟶ b) :
    simplexFiberDiagramMap f h ≫ simplexLeftFiberProjection f b.unop.val =
      simplexLeftFiberProjection f a.unop.val := simplexLeftFiberLift_projection _ _ _ _ _

/-- 概要：左 fiber の射のパラメーターは単体の射との合成。
方針：pullback の第二射影の式。
規約：全単体での等号。使われ方：図式の恒等・合成則。 -/
lemma simplexFiberDiagramMap_parameter {X Y : SSet.{u}} (f : X ⟶ Y)
    {a b : Y.Elementsᵒᵖ} (h : a ⟶ b) :
    simplexFiberDiagramMap f h ≫ simplexLeftFiberParameter f b.unop.val =
      simplexLeftFiberParameter f a.unop.val ≫ stdSimplex.map h.unop.hom.unop :=
  simplexLeftFiberLift_parameter _ _ _ _ _

/-- 概要：strict 左 fiber を単体圏上の共変図式に束ねる。
方針：二射影で単体の射の恒等・合成則を確認する。
規約：homotopy fiber の代替ではない。使われ方：単体積版 Quillen A の解消。 -/
def simplexFiberDiagram {X Y : SSet.{u}} (f : X ⟶ Y) : Y.Elementsᵒᵖ ⥤ SSet.{u} where
  obj a := simplexLeftFiber f a.unop.val
  map h := simplexFiberDiagramMap f h
  map_id a := by
    apply simplexLeftFiber_hom_ext f a.unop.val
    · rw [simplexFiberDiagramMap_projection, Category.id_comp]
    · rw [simplexFiberDiagramMap_parameter, Category.id_comp]
      change _ ≫ stdSimplex.map (𝟙 a.unop.obj.unop) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
  map_comp h k := by
    apply simplexLeftFiber_hom_ext f _
    · rw [simplexFiberDiagramMap_projection, Category.assoc,
        simplexFiberDiagramMap_projection, simplexFiberDiagramMap_projection]
    · rw [simplexFiberDiagramMap_parameter, Category.assoc,
        simplexFiberDiagramMap_parameter, ← Category.assoc, simplexFiberDiagramMap_parameter]
      change _ ≫ stdSimplex.map (h.unop.hom.unop ≫ k.unop.hom.unop) = _
      rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：元の X への射影を単体圏上の自然な族に束ねる。
方針：各左 fiber の第一射影を取る。
規約：全ての単体の射で自然。使われ方：解消から X への augmentation。 -/
def simplexFiberProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplexFiberDiagram f ⟶ (CategoryTheory.Functor.const Y.Elementsᵒᵖ).obj X where
  app a := simplexLeftFiberProjection f a.unop.val
  naturality {a b} h := by
    change simplexFiberDiagramMap f h ≫ simplexLeftFiberProjection f b.unop.val =
      simplexLeftFiberProjection f a.unop.val ≫ 𝟙 X
    rw [Category.comp_id]
    exact simplexFiberDiagramMap_projection f h

/-- 概要：左 fiber から固定した Z への射を単体圏上の自然変換にする。
方針：元の X への射影に g:X→Z を後合成する。
規約：g の弱同値性は仮定しない。使われ方：Quillen A の対象ごとの比較。 -/
def simplexFiberPostcomp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    simplexFiberDiagram f ⟶ (CategoryTheory.Functor.const Y.Elementsᵒᵖ).obj Z where
  app a := simplexLeftFiberProjection f a.unop.val ≫ g
  naturality {a b} h := by
    change simplexFiberDiagramMap f h ≫ (simplexLeftFiberProjection f b.unop.val ≫ g) =
      (simplexLeftFiberProjection f a.unop.val ≫ g) ≫ 𝟙 Z
    rw [Category.comp_id, ← Category.assoc, simplexFiberDiagramMap_projection]

end SerrePositivity.KST.SConstruction
