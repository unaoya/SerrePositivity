module
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-! # 標準ホーンの宇宙比較

概要：全ての標準ホーンの ULift は大きい宇宙の同じホーンと実同型。
方針：所属条件を同じ順序写像の像で判定し、単体作用を照合する。
規約：内側・外側の両方を含む。使われ方：span/cospan と普遍四角形の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- ホーンの単体を同じ順序写像のまま上げる。 -/
def uliftHornSimplexUp (n : ℕ) (i : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (s : (horn n i : SSet.{u}).obj d) : (horn n i : SSet.{max u v}).obj d :=
  ⟨ULift.up s.val.down, by
    have hs := s.property
    rw [mem_horn_iff] at hs ⊢
    exact hs⟩

/-- ホーンの単体を同じ順序写像のまま下げる。 -/
def uliftHornSimplexDown (n : ℕ) (i : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (s : (horn n i : SSet.{max u v}).obj d) : (horn n i : SSet.{u}).obj d :=
  ⟨ULift.up s.val.down, by
    have hs := s.property
    rw [mem_horn_iff] at hs ⊢
    exact hs⟩

/-- 標準ホーンの持ち上げと大きい宇宙の同じホーンとの実同型。 -/
def uliftHornIso (n : ℕ) (i : Fin (n + 1)) :
    (SSet.uliftFunctor.{v, u}).obj (horn n i : SSet.{u}) ≅
      (horn n i : SSet.{max u v}) where
  hom := {
    app d := ↾fun s => uliftHornSimplexUp n i d s.down
    naturality _ _ _ := by ext s; rfl }
  inv := {
    app d := ↾fun s => ULift.up (uliftHornSimplexDown n i d s)
    naturality _ _ _ := by ext s; rfl }
  hom_inv_id := by ext d s; rfl
  inv_hom_id := by ext d s; rfl

/-- ホーンの同型は周囲の標準単体への包含を保つ。 -/
lemma uliftHornIso_ι (n : ℕ) (i : Fin (n + 1)) :
    (uliftHornIso.{u, v} n i).hom ≫ (horn.{max u v} n i).ι =
      (SSet.uliftFunctor.{v, u}).map (horn.{u} n i).ι ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom := rfl

/-- ホーンの同型は全ての存在する面の包含を保つ。 -/
lemma uliftHornIso_face {n : ℕ} (i j : Fin (n + 2)) (h : j ≠ i) :
    (SSet.uliftFunctor.{v, u}).map (horn.ι i j h) ≫ (uliftHornIso (n + 1) i).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom ≫
        (horn.ι i j h : (Δ[n] : SSet.{max u v}) ⟶ horn (n + 1) i) := by
  ext d s
  rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
