module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary

/-! # 標準境界の宇宙持ち上げ

概要：標準境界の ULift と大きい宇宙の同じ境界は実単体的同型。
方針：単体を表す同じ順序写像を送り、境界所属の像の非全射性を保つ。
規約：零次元の空境界を含む。使われ方：始・終対象の全境界充填の宇宙比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 境界の単体を順序写像を変えずに上げる。 -/
def uliftBoundarySimplexUp (n : ℕ) (d : SimplexCategoryᵒᵖ)
    (s : (∂Δ[n] : SSet.{u}).obj d) : (∂Δ[n] : SSet.{max u v}).obj d :=
  ⟨ULift.up s.val.down, by
    have hs := s.property
    rw [mem_boundary_iff_notMem_range] at hs ⊢
    exact hs⟩

/-- 境界の単体を順序写像を変えずに下げる。 -/
def uliftBoundarySimplexDown (n : ℕ) (d : SimplexCategoryᵒᵖ)
    (s : (∂Δ[n] : SSet.{max u v}).obj d) : (∂Δ[n] : SSet.{u}).obj d :=
  ⟨ULift.up s.val.down, by
    have hs := s.property
    rw [mem_boundary_iff_notMem_range] at hs ⊢
    exact hs⟩

/-- 標準境界の宇宙持ち上げは大きい宇宙の同じ境界と実同型。 -/
def uliftBoundaryIso (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (∂Δ[n] : SSet.{u}) ≅
      (∂Δ[n] : SSet.{max u v}) where
  hom := {
    app d := ↾fun s => uliftBoundarySimplexUp n d s.down
    naturality _ _ α := by
      ext s
      rfl }
  inv := {
    app d := ↾fun s => ULift.up (uliftBoundarySimplexDown n d s)
    naturality _ _ α := by
      ext s
      rfl }
  hom_inv_id := by
    ext d s
    rfl
  inv_hom_id := by
    ext d s
    rfl

/-- 境界の宇宙同型は周囲の標準単体への包含と可換。 -/
lemma uliftBoundaryIso_ι (n : ℕ) :
    (uliftBoundaryIso.{u, v} n).hom ≫ (boundary.{max u v} n).ι =
      (SSet.uliftFunctor.{v, u}).map (boundary.{u} n).ι ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom := rfl

/-- 境界の宇宙同型は指定頂点を保持する。 -/
lemma uliftBoundaryIso_vertex (n : ℕ) (i : Fin (n + 2)) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i) ≫ (uliftBoundaryIso n.succ).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 0).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i :
        (Δ[0] : SSet.{max u v}) ⟶ ∂Δ[n + 1]) := by
  ext d s
  rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
