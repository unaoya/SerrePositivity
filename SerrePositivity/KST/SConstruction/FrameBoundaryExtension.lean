module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroBoundaryExtension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialPrismBoundary

/-! # 枠の図式の族の相対境界延長
概要：既存の部分図式と境界上の族を固定して、普遍的な端点で枠を補完する。
方針：直積の和部分複体を貼り合わせ、混合始点・終点延長を適用する。
規約：正次元の境界を扱う。使われ方：第一行に零対角を追加する持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：境界上の図式の族は、既存部分への制限を保って枠へ延長できる。
方針：新しい積単体の始点か終点に、境界上の普遍性を移す。
規約：単体ごとに端点を選べる。値域の quasicategory 性は不要。
使われ方：BGT Lemma 7.3 の零対角の相対境界充填。 -/
lemma frame_extend_boundary {B X : SSet.{u}} (S : B.Subcomplex) (n : ℕ)
    (H : B ⊗ (boundary (n + 1) : SSet.{u}) ⟶ X)
    (G : (S : SSet.{u}) ⊗ Δ[n + 1] ⟶ X)
    (hw : (S.ι ▷ (boundary (n + 1) : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ (boundary (n + 1)).ι) ≫ G)
    (ht : ∀ (m : ℕ) (s : B _⦋m + 1⦌), s ∉ S.obj (Opposite.op ⦋m + 1⦌) →
      (∀ v : (boundary (n + 1) : SSet.{u}) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (H.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, v))) ∨
      (∀ v : (boundary (n + 1) : SSet.{u}) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (H.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, v)))) :
    ∃ F : B ⊗ Δ[n + 1] ⟶ X,
      (B ◁ (boundary (n + 1)).ι) ≫ F = H ∧ (S.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ F = G := by
  let T := boundary.{u} (n + 1)
  let q := Subcomplex.unionProd.isPushout S T
  let a := q.desc H G hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a = G := q.inr_desc _ _ _
  let A := Subcomplex.unionProd S T
  have hA : ∀ v : (B ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌,
      v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    apply Or.inl
    refine ⟨by trivial, ?_⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hend (m : ℕ) (s : (B ⊗ (Δ[n + 1] : SSet.{u})) _⦋m + 1⦌)
      (hs : s ∉ A.obj (Opposite.op ⦋m + 1⦌)) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hA _⟩) ∨
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩) := by
    have hs₁ : s.1 ∉ S.obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs (Or.inr ⟨h, by trivial⟩)
    have he (v : (B ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌) :
        a.app (Opposite.op ⦋0⦌) ⟨v, hA v⟩ = H.app (Opposite.op ⦋0⦌)
          (v.1, ⟨v.2, by
            have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
            rw [Equiv.symm_apply_apply] at h
            exact h⟩) := by
      let w : (B ⊗ (T : SSet.{u})) _⦋0⦌ := (v.1, ⟨v.2, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩)
      exact ConcreteCategory.congr_hom (NatTrans.congr_app ha₁ (Opposite.op ⦋0⦌)) w
    rcases ht m s.1 hs₁ with hi | ht
    · left
      rw [he]
      exact hi _
    · right
      rw [he]
      exact ht _
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_of_initial_or_terminal_endpoints A hA a hend
  refine ⟨F, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
  · rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, hF, ha₂]

end SerrePositivity.KST.SConstruction
