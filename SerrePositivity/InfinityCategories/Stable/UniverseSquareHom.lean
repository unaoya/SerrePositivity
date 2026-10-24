module

public import SerrePositivity.InfinityCategories.Stable.Pointed
public import SerrePositivity.InfinityCategories.Stable.UniverseUniversalSquares

/-! # 四角形の全写像と辺の宇宙比較

概要：持ち上げ先の全ての四角形は一意に降下し、頂点と指定辺は保たれる。
方針：正方形の実同型と ULift 関手の完全忠実性を使う。
規約：辺の端点も実等式で固定。使われ方：fiber/cofiber の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits MonoidalCategory
open scoped Simplicial

/-- 四角形の全写像の宇宙比較。 -/
def uliftSquareHomEquiv (X : SSet.{u}) :
    (Δ[1] ⊗ Δ[1] ⟶ X) ≃
      ((Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X) where
  toFun := uliftSquare
  invFun G := (SSet.uliftFunctor.{v, u}).preimage (uliftSquareIso.hom ≫ G)
  left_inv F := by
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [Functor.map_preimage]
    exact Iso.hom_inv_id_assoc uliftSquareIso ((SSet.uliftFunctor.{v, u}).map F)
  right_inv G := by
    change uliftSquareIso.inv ≫ (SSet.uliftFunctor.{v, u}).map
      ((SSet.uliftFunctor.{v, u}).preimage (uliftSquareIso.hom ≫ G)) = G
    rw [(SSet.uliftFunctor.{v, u}).map_preimage, Iso.inv_hom_id_assoc]

/-- 四角形の持ち上げは全ての角の実頂点を保持する。 -/
lemma uliftSquare_vertex {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) (i j : Fin 2) :
    squareVertex (uliftSquare.{u, v} F) i j = ULift.up (squareVertex F i j) := rfl

/-- 四角形の持ち上げは右辺を保持する。 -/
lemma uliftSquare_rightEdge {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    squareRightEdge ≫ uliftSquare.{u, v} F =
      uliftSimplexHomEquiv X 1 (squareRightEdge ≫ F) := by
  ext d s
  rfl

/-- 四角形の持ち上げは底辺を保持する。 -/
lemma uliftSquare_bottomEdge {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    squareBottomEdge ≫ uliftSquare.{u, v} F =
      uliftSimplexHomEquiv X 1 (squareBottomEdge ≫ F) := by
  ext d s
  rfl

/-- 端点を指定した実辺を持ち上げる。 -/
def uliftEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X))
      (ULift.up x) (ULift.up y) where
  edge := ULift.up f.edge
  src_eq := congrArg ULift.up f.src_eq
  tgt_eq := congrArg ULift.up f.tgt_eq

/-- 辺の持ち上げと Yoneda の実辺写像は一致する。 -/
lemma uliftEdge_yoneda {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    SSet.yonedaEquiv.symm (uliftEdge.{u, v} f).edge =
      uliftSimplexHomEquiv X 1 (SSet.yonedaEquiv.symm f.edge) :=
  (uliftYonedaMap f.edge).symm

end SerrePositivity.InfinityCategories
