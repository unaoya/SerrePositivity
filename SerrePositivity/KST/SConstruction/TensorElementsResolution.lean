module
public import SerrePositivity.KST.SConstruction.ElementsResolutionRows
public import Mathlib.Logic.Equiv.Prod

/-! # 二重単体解消と固定係数との積
概要：固定した単体集合との積を要素の圏による解消の外へ取り出す。
方針：底の射列と最後のラベルの表示で二つのラベルを分ける。
規約：単体集合の実際の同型。使われ方：元のパラメーターを保った積版 Quillen A。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.MonoidalCategory SSet
open scoped Simplicial

/-- 単体集合値図式の各対象を固定係数と積にする。 -/
def tensorCoefficientDiagram {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) (Z : SSet.{max u v}) : J ⥤ SSet.{max u v} :=
  F ⋙ (tensoringRight _).obj Z

/-- 積係数の第一射影は底の図式に関して自然。 -/
def tensorCoefficientProjection {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) (Z : SSet.{max u v}) : tensorCoefficientDiagram F Z ⟶ F where
  app _j := { app := fun _n => ↾Prod.fst, naturality := fun {_n _m} _h => rfl }
  naturality {_j _k} _h := rfl

/-- 積係数の解消から、解消と固定係数の積への比較。 -/
def tensorElementsResolutionComparison {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) (Z : SSet.{max u v}) :
    SerrePositivity.BisimplicialModel.diagonal.obj
      (elementsResolution (tensorCoefficientDiagram F Z)) ⟶
    SerrePositivity.BisimplicialModel.diagonal.obj (elementsResolution F) ⊗ Z where
  app n := ↾fun c =>
    ⟨c ⋙ ((tensorCoefficientProjection F Z).flipApp n).mapElements.op,
      (c.obj (Fin.last n.unop.len)).unop.val.2⟩
  naturality {n l} h := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Prod.ext
    · rfl
    · change Z.map h (c.obj (h.unop.toOrderHom (Fin.last l.unop.len))).unop.val.2 =
        Z.map h (c.obj (Fin.last n.unop.len)).unop.val.2
      apply congrArg (Z.map h)
      exact (congrArg Prod.snd (c.map (homOfLE (Fin.le_last
        (h.unop.toOrderHom (Fin.last l.unop.len))))).unop.map_val).symm

/-- 積係数の射列の同値を、底の射列と二つの最後のラベルの分離で構成する。 -/
def tensorElementsResolutionEquiv {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) (Z : SSet.{max u v}) (n : SimplexCategoryᵒᵖ) :
    (SerrePositivity.BisimplicialModel.diagonal.obj
      (elementsResolution (tensorCoefficientDiagram F Z))).obj n ≃
    ((SerrePositivity.BisimplicialModel.diagonal.obj (elementsResolution F)) ⊗ Z).obj n :=
  (oppositeLabelledChainEquiv ((tensorCoefficientDiagram F Z).flip.obj n) n.unop.len).trans
    ((Equiv.sigmaProdDistrib
      (fun c : ComposableArrows Jᵒᵖ n.unop.len => F.obj (c.obj (Fin.last n.unop.len)).unop |>.obj n)
      (Z.obj n)).symm.trans
        (Equiv.prodCongr (oppositeLabelledChainEquiv (F.flip.obj n) n.unop.len).symm
          (Equiv.refl _)))

/-- 解消の積への比較はラベル分離による同値と一致する。 -/
lemma tensorElementsResolutionComparison_eq {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) (Z : SSet.{max u v}) (n : SimplexCategoryᵒᵖ) :
    ((tensorElementsResolutionComparison F Z).app n : _ → _) =
      tensorElementsResolutionEquiv F Z n := by
  funext c
  apply Prod.ext
  · apply (oppositeLabelledChainEquiv (F.flip.obj n) n.unop.len).injective
    change _ = (oppositeLabelledChainEquiv (F.flip.obj n) n.unop.len)
      ((oppositeLabelledChainEquiv (F.flip.obj n) n.unop.len).symm _)
    rw [Equiv.apply_symm_apply]
    rfl
  · rfl

/-- 積係数の二重単体解消の対角は解消と固定係数の積に同型。 -/
def tensorElementsResolutionIso {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) (Z : SSet.{max u v}) :
    SerrePositivity.BisimplicialModel.diagonal.obj
      (elementsResolution (tensorCoefficientDiagram F Z)) ≅
    SerrePositivity.BisimplicialModel.diagonal.obj (elementsResolution F) ⊗ Z := by
  have (n : SimplexCategoryᵒᵖ) : IsIso ((tensorElementsResolutionComparison F Z).app n) := by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    rw [tensorElementsResolutionComparison_eq]
    exact (tensorElementsResolutionEquiv F Z n).bijective
  have : IsIso (tensorElementsResolutionComparison F Z) := NatIso.isIso_of_isIso_app _
  exact asIso (tensorElementsResolutionComparison F Z)

end SerrePositivity.KST.SConstruction
