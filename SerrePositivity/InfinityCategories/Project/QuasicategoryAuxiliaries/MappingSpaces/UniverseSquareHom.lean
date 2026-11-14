module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseBoundaryHom
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSquareShape

/-! # 四角形の全写像と辺の宇宙比較

概要：持ち上げ先の全ての四角形は一意に降下し、頂点と指定辺は保たれる。
方針：正方形の実同型と ULift 関手の完全忠実性を使う。
規約：辺の端点も実等式で固定。使われ方：fiber/cofiber の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet MonoidalCategory
open scoped _root_.Simplicial

/-- 四角形の全写像の宇宙比較。 -/
def uliftSquareHomEquiv (X : SSet.{u}) :
    (Δ[1] ⊗ Δ[1] ⟶ X) ≃
      ((Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X) where
  toFun := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare
  invFun G := (SSet.uliftFunctor.{v, u}).preimage (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.hom ≫ G)
  left_inv F := by
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [Functor.map_preimage]
    exact Iso.hom_inv_id_assoc _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso ((SSet.uliftFunctor.{v, u}).map F)
  right_inv G := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.inv ≫ (SSet.uliftFunctor.{v, u}).map
      ((SSet.uliftFunctor.{v, u}).preimage (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.hom ≫ G)) = G
    rw [(SSet.uliftFunctor.{v, u}).map_preimage, Iso.inv_hom_id_assoc]

/-- 四角形の持ち上げは全ての角の実頂点を保持する。 -/
lemma uliftSquare_vertex {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, v} F) i j = ULift.up (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j) := rfl

/-- 四角形の持ち上げは右辺を保持する。 -/
lemma uliftSquare_rightEdge {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, v} F =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv X 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) := by
  ext d s
  rfl

/-- 四角形の持ち上げは底辺を保持する。 -/
lemma uliftSquare_bottomEdge {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, v} F =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv X 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F) := by
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
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv X 1 (SSet.yonedaEquiv.symm f.edge) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap f.edge).symm

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
