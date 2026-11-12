module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseBoundary

/-! # 標準単体と境界からの射の宇宙比較

概要：境界・単体からの全写像を全単射で比較し、頂点固定と充填の方程式を保つ。
方針：形状の実同型と ULift の完全忠実性を使う。
規約：始・終対象性を仮定しない。使われ方：全正次元境界の充填の宇宙移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 標準単体からの全写像の宇宙比較。 -/
def uliftSimplexHomEquiv (X : SSet.{u}) (n : ℕ) :
    ((Δ[n] : SSet.{u}) ⟶ X) ≃
      ((Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X) where
  toFun F := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map F
  invFun G := (SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom ≫ G)
  left_inv F := by
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [Functor.map_preimage, Iso.hom_inv_id_assoc]
  right_inv G := by
    change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map
      ((SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom ≫ G)) = G
    rw [(SSet.uliftFunctor.{v, u}).map_preimage, Iso.inv_hom_id_assoc]

/-- 標準境界からの全写像の宇宙比較。 -/
def uliftBoundaryHomEquiv (X : SSet.{u}) (n : ℕ) :
    ((∂Δ[n] : SSet.{u}) ⟶ X) ≃
      ((∂Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X) where
  toFun F := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map F
  invFun G := (SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso.{u, v} n).hom ≫ G)
  left_inv F := by
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [Functor.map_preimage, Iso.hom_inv_id_assoc]
  right_inv G := by
    change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map
      ((SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso.{u, v} n).hom ≫ G)) = G
    rw [(SSet.uliftFunctor.{v, u}).map_preimage, Iso.inv_hom_id_assoc]

/-- 単体の宇宙比較は境界への制限と可換。 -/
lemma uliftSimplexHomEquiv_boundary (X : SSet.{u}) (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X) :
    (boundary.{max u v} n).ι ≫ uliftSimplexHomEquiv.{u, v} X n F =
      uliftBoundaryHomEquiv X n ((boundary.{u} n).ι ≫ F) := by
  ext d s
  rfl

/-- 境界の宇宙比較は指定頂点への制限と可換。 -/
lemma uliftBoundaryHomEquiv_vertex (X : SSet.{u}) (n : ℕ) (i : Fin (n + 2))
    (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i : (Δ[0] : SSet.{max u v}) ⟶ _) ≫
        uliftBoundaryHomEquiv.{u, v} X (n + 1) b =
      uliftSimplexHomEquiv X 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i ≫ b) := by
  ext d s
  rfl

/-- 零単体の Yoneda 写像の宇宙比較は元の零単体を ULift する。 -/
lemma uliftSimplexHomEquiv_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    uliftSimplexHomEquiv.{u, v} X 0 (SSet.yonedaEquiv.symm x) =
      SSet.yonedaEquiv.symm (ULift.up x) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap x

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
