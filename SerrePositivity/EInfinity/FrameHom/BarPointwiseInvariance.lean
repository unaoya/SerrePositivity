module

public import SerrePositivity.EInfinity.FrameHom.BarRowsCoproduct
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
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.EInfinity.FrameHom.BarRows
open SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}}

/-- 元の bar の自然変換を転置した各行の射。 -/
abbrev rowMap (η : F ⟶ G) (n : SimplexCategoryᵒᵖ) : row F n ⟶ row G n :=
  ((flipFunctor _ _ _).map ((BarConstruction.rows D).map η)).app n

/-- 射列の持ち上げは、元の図式の比較と可換。 -/
lemma inclusion_rowMap (η : F ⟶ G) (n : SimplexCategoryᵒᵖ)
    (c : ComposableArrows D n.unop.len) :
    inclusion F n c ≫ rowMap η n =
      SSet.uliftFunctor.{max uD vD, v}.map (η.app (c.obj 0)) ≫ inclusion G n c := by
  ext m x
  exact LabelledChain.map (F.flip.obj m) c x.down
    (Functor.whiskerRight η ((evaluation SimplexCategoryᵒᵖ (Type v)).obj m))

/-- 成分ごとの反転性を、元の転置した行の射へ移す。 -/
lemma rowMap_localized_isIso (η : F ⟶ G)
    (hη : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (η.app d)))
    (n : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (rowMap η n)) := by
  exact KanLocalizedCoproducts.actual_localized_isIso
    (ComposableArrows D n.unop.len)
    (fun c => SSet.uliftFunctor.{max uD vD, v}.map (η.app (c.obj 0)))
    (fun c => UniverseLift.anodyneQ_map_isIso_of_small _ (hη (c.obj 0)))
    (cofan F n) (cofan G n) (isColimit F n) (isColimit G n) (rowMap η n)
    (inclusion_rowMap η n)

/-- 二方向を交換した対角と元の対角の、恒等成分による同型。 -/
def diagonalFlipIso (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) :
    BisimplicialModel.diagonal.obj B.flip ≅ BisimplicialModel.diagonal.obj B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    change (B.obj n).map θ ≫ (B.map θ).app m ≫ 𝟙 _ =
      𝟙 _ ≫ (B.map θ).app n ≫ (B.obj m).map θ
    simpa only [Category.comp_id, Category.id_comp] using (B.map θ).naturality θ)

/-- 対角交換の同型は元の自然変換を保つ。 -/
lemma diagonalFlipIso_naturality {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (η : B ⟶ B') :
    BisimplicialModel.diagonal.map ((flipFunctor _ _ _).map η) ≫
        (diagonalFlipIso B').hom =
      (diagonalFlipIso B).hom ≫ BisimplicialModel.diagonal.map η := by
  ext n x
  rfl

/-- 同じ bar 関手は各成分で局所化可逆な自然変換を局所化可逆にする。 -/
lemma map_localized_isIso (η : F ⟶ G)
    (hη : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (η.app d))) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((BarConstruction.functor D).map η)) := by
  have h := BisimplicialModel.localized_diagonal_map
    ((flipFunctor _ _ _).map ((BarConstruction.rows D).map η))
    (rowMap_localized_isIso η hη)
  have eq := congrArg AnodyneHomotopy.anodyneQ.map
    (diagonalFlipIso_naturality ((BarConstruction.rows D).map η))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at eq
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map
      ((diagonalFlipIso ((BarConstruction.rows D).obj F)).hom) ≫
      AnodyneHomotopy.anodyneQ.map ((BarConstruction.functor D).map η)) :=
    eq ▸ inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map
      (BisimplicialModel.diagonal.map
        ((flipFunctor _ _ _).map ((BarConstruction.rows D).map η))) ≫
      AnodyneHomotopy.anodyneQ.map
        (diagonalFlipIso ((BarConstruction.rows D).obj G)).hom))
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.EInfinity.FrameHom.BarRows
