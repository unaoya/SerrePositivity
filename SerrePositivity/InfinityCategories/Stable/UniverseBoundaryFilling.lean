module
public import SerrePositivity.InfinityCategories.Stable.UniverseBoundaryHom

/-! # 頂点固定の全境界充填の宇宙比較

概要：指定頂点を保つ境界の充填は ULift の前後で存在が同値。
方針：境界と単体からの全写像の全単射を、二つの方程式と同時に移す。
規約：全正次元・全頂点番号を扱う。使われ方：始・終対象性の保存と反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 境界の指定頂点を固定する方程式は宇宙比較で保ち反映される。 -/
lemma uliftBoundary_vertex_condition_iff {X : SSet.{u}} (x : X _⦋0⦌)
    (n : ℕ) (i : Fin (n + 2)) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) :
    boundaryVertex n i ≫ b = SSet.yonedaEquiv.symm x ↔
      (boundaryVertex n i : (Δ[0] : SSet.{max u v}) ⟶ _) ≫
        uliftBoundaryHomEquiv.{u, v} X (n + 1) b =
          SSet.yonedaEquiv.symm (ULift.up x) := by
  rw [uliftBoundaryHomEquiv_vertex, ← uliftSimplexHomEquiv_vertex x]
  exact (uliftSimplexHomEquiv.{u, v} X 0).injective.eq_iff.symm

/-- 境界を厳密に保つ充填の存在は宇宙比較で同値。 -/
lemma uliftBoundary_filling_iff {X : SSet.{u}} (n : ℕ)
    (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) :
    (∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = b) ↔
      ∃ F : (Δ[n + 1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X,
        (boundary (n + 1)).ι ≫ F = uliftBoundaryHomEquiv X (n + 1) b := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨uliftSimplexHomEquiv X (n + 1) F,
      (uliftSimplexHomEquiv_boundary X (n + 1) F).trans
        (congrArg (uliftBoundaryHomEquiv X (n + 1)) hF)⟩
  · rintro ⟨F, hF⟩
    obtain ⟨G, rfl⟩ := (uliftSimplexHomEquiv.{u, v} X (n + 1)).surjective F
    exact ⟨G, (uliftBoundaryHomEquiv X (n + 1)).injective
      ((uliftSimplexHomEquiv_boundary X (n + 1) G).symm.trans hF)⟩

/-- 頂点番号を指定した全正次元境界の充填性は宇宙比較で同値。 -/
lemma uliftBoundary_filling_at_vertex_iff {X : SSet.{u}} (x : X _⦋0⦌)
    (i : ∀ n : ℕ, Fin (n + 2)) :
    (∀ n (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X),
      boundaryVertex n (i n) ≫ b = SSet.yonedaEquiv.symm x →
      ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = b) ↔
    (∀ n (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X),
      boundaryVertex n (i n) ≫ b = SSet.yonedaEquiv.symm (ULift.up x) →
      ∃ F : (Δ[n + 1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X,
        (boundary (n + 1)).ι ≫ F = b) := by
  constructor
  · intro h n b hb
    obtain ⟨b, rfl⟩ := (uliftBoundaryHomEquiv.{u, v} X (n + 1)).surjective b
    exact (uliftBoundary_filling_iff.{u, v} n b).1
      (h n b ((uliftBoundary_vertex_condition_iff x n (i n) b).2 hb))
  · intro h n b hb
    exact (uliftBoundary_filling_iff.{u, v} n b).2
      (h n (uliftBoundaryHomEquiv X (n + 1) b)
        ((uliftBoundary_vertex_condition_iff x n (i n) b).1 hb))

end SerrePositivity.InfinityCategories
