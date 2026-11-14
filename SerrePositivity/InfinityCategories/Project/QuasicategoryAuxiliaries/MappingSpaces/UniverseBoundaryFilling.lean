module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseBoundaryHom

/-! # 頂点固定の全境界充填の宇宙比較

概要：指定頂点を保つ境界の充填は ULift の前後で存在が同値。
方針：境界と単体からの全写像の全単射を、二つの方程式と同時に移す。
規約：全正次元・全頂点番号を扱う。使われ方：始・終対象性の保存と反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 境界の指定頂点を固定する方程式は宇宙比較で保ち反映される。 -/
lemma uliftBoundary_vertex_condition_iff {X : SSet.{u}} (x : X _⦋0⦌)
    (n : ℕ) (i : Fin (n + 2)) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i ≫ b = SSet.yonedaEquiv.symm x ↔
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i : (Δ[0] : SSet.{max u v}) ⟶ _) ≫
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryHomEquiv.{u, v} X (n + 1) b =
          SSet.yonedaEquiv.symm (ULift.up x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryHomEquiv_vertex, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv_vertex x]
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{u, v} X 0).injective.eq_iff.symm

/-- 境界を厳密に保つ充填の存在は宇宙比較で同値。 -/
lemma uliftBoundary_filling_iff {X : SSet.{u}} (n : ℕ)
    (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) :
    (∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = b) ↔
      ∃ F : (Δ[n + 1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X,
        (boundary (n + 1)).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryHomEquiv X (n + 1) b := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv X (n + 1) F,
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv_boundary X (n + 1) F).trans
        (congrArg (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryHomEquiv X (n + 1)) hF)⟩
  · rintro ⟨F, hF⟩
    obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{u, v} X (n + 1)).surjective F
    exact ⟨G, (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryHomEquiv X (n + 1)).injective
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv_boundary X (n + 1) G).symm.trans hF)⟩

/-- 頂点番号を指定した全正次元境界の充填性は宇宙比較で同値。 -/
lemma uliftBoundary_filling_at_vertex_iff {X : SSet.{u}} (x : X _⦋0⦌)
    (i : ∀ n : ℕ, Fin (n + 2)) :
    (∀ n (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (i n) ≫ b = SSet.yonedaEquiv.symm x →
      ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = b) ↔
    (∀ n (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (i n) ≫ b = SSet.yonedaEquiv.symm (ULift.up x) →
      ∃ F : (Δ[n + 1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X,
        (boundary (n + 1)).ι ≫ F = b) := by
  constructor
  · intro h n b hb
    obtain ⟨b, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryHomEquiv.{u, v} X (n + 1)).surjective b
    exact (uliftBoundary_filling_iff.{u, v} n b).1
      (h n b ((uliftBoundary_vertex_condition_iff x n (i n) b).2 hb))
  · intro h n b hb
    exact (uliftBoundary_filling_iff.{u, v} n b).2
      (h n (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryHomEquiv X (n + 1) b)
        ((uliftBoundary_vertex_condition_iff x n (i n) b).1 hb))

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
