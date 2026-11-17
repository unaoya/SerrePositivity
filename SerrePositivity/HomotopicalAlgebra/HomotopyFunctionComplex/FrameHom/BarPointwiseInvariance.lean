module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRowsCoproduct
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne

/-!
# 各成分で反転可能な図式の比較の bar 不変性

## 概要
既存の bar 関手は、anodyne 局所化で各成分が可逆な自然変換を可逆にする。

## 方針（定義・証明）
転置した各行の余積表示に成分ごとの反転性を適用し、対角比較を使う。
二方向の交換の同型で元の bar の射そのものへ戻す。

## 規約と注意
添字・値の宇宙は独立。単体集合のモデル構造や図式の cofibrancy は仮定しない。

## 使われ方
固定右脚の Hom と、全右脚を走る bar の比較に使う。
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows
open _root_.SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}}

/-- 元の bar の自然変換を転置した各行の射。 -/
abbrev rowMap (η : F ⟶ G) (n : SimplexCategoryᵒᵖ) : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.row F n ⟶ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.row G n :=
  ((flipFunctor _ _ _).map ((BarConstruction.rows D).map η)).app n

/-- 射列の持ち上げは、元の図式の比較と可換。 -/
lemma inclusion_rowMap (η : F ⟶ G) (n : SimplexCategoryᵒᵖ)
    (c : ComposableArrows D n.unop.len) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.inclusion F n c ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.rowMap η n =
      SSet.uliftFunctor.{max uD vD, v}.map (η.app (c.obj 0)) ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.inclusion G n c := by
  ext m x
  exact _root_.SerrePositivity.LabelledChain.map (F.flip.obj m) c x.down
    (Functor.whiskerRight η ((evaluation SimplexCategoryᵒᵖ (Type v)).obj m))

/-- 成分ごとの反転性を、元の転置した行の射へ移す。 -/
lemma rowMap_localized_isIso (η : F ⟶ G)
    (hη : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (η.app d)))
    (n : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.rowMap η n)) := by
  exact KanLocalizedCoproducts.actual_localized_isIso
    (ComposableArrows D n.unop.len)
    (fun c => SSet.uliftFunctor.{max uD vD, v}.map (η.app (c.obj 0)))
    (fun c => UniverseLift.anodyneQ_map_isIso_of_small _ (hη (c.obj 0)))
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.cofan F n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.cofan G n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.isColimit F n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.isColimit G n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.rowMap η n)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.inclusion_rowMap η n)

/-- 二方向を交換した対角と元の対角の、恒等成分による同型。 -/
def diagonalFlipIso (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) :
    _root_.SerrePositivity.BisimplicialModel.diagonal.obj B.flip ≅ _root_.SerrePositivity.BisimplicialModel.diagonal.obj B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    change (B.obj n).map θ ≫ (B.map θ).app m ≫ 𝟙 _ =
      𝟙 _ ≫ (B.map θ).app n ≫ (B.obj m).map θ
    simpa only [Category.comp_id, Category.id_comp] using (B.map θ).naturality θ)

/-- 対角交換の同型は元の自然変換を保つ。 -/
lemma diagonalFlipIso_naturality {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (η : B ⟶ B') :
    _root_.SerrePositivity.BisimplicialModel.diagonal.map ((flipFunctor _ _ _).map η) ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso B').hom =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso B).hom ≫ _root_.SerrePositivity.BisimplicialModel.diagonal.map η := by
  ext n x
  rfl

/-- 同じ bar 関手は各成分で局所化可逆な自然変換を局所化可逆にする。 -/
lemma map_localized_isIso (η : F ⟶ G)
    (hη : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (η.app d))) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((BarConstruction.functor D).map η)) := by
  have h := _root_.SerrePositivity.BisimplicialModel.localized_diagonal_map
    ((flipFunctor _ _ _).map ((BarConstruction.rows D).map η))
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.rowMap_localized_isIso η hη)
  have eq := congrArg AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso_naturality ((BarConstruction.rows D).map η))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at eq
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map
      ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso ((BarConstruction.rows D).obj F)).hom) ≫
      AnodyneHomotopy.anodyneQ.map ((BarConstruction.functor D).map η)) :=
    eq ▸ inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.BisimplicialModel.diagonal.map
        ((flipFunctor _ _ _).map ((BarConstruction.rows D).map η))) ≫
      AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso ((BarConstruction.rows D).obj G)).hom))
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows
