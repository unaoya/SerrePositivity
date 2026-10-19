module
public import SerrePositivity.KST.SConstruction.BoundaryPathKClass
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroMap

/-! # 実際の零次 K 群の対象類による生成
概要：三角圏 K₀ から実際の BF 零次 K 群への既存の比較準同型が全射である。
方針：元の辺を object S₁ の辺へ帰着し、基本亜群の辺・逆・合成の帰納法を使う。
規約：単射性と関係の完全性は別途必要。使われ方：π₀ K 比較の逆写像の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 元の基本亜群の任意の道の K 類は、三角圏 K₀ 比較の像に属する。 -/
lemma boundaryPathKClass_mem_triangulatedKZeroRange (X : StableModel.{u})
    {x y : boundaryFundamentalGroupoid X} (f : x ⟶ y) :
    boundaryPathKClass X (singletonCategoryHom (boundaryFundamentalBasepoint X) f) ∈
      (triangulatedKZeroMap X).range := by
  apply simplicialFundamentalGroupoid_hom_rec (boundaryReducedRealization 0 X).right
    (P := fun f => boundaryPathKClass X
      (singletonCategoryHom (boundaryFundamentalBasepoint X) f) ∈
        (triangulatedKZeroMap X).range) (f := f)
  · intro x y e
    rw [singletonCategoryHom_boundary_edge]
    rcases rawBoundaryPath_cases X e.edge with he | ⟨d, hd⟩
    · rw [he, boundaryPathKClass_id]
      exact (triangulatedKZeroMap X).range.zero_mem
    · rw [hd, boundaryPathKClass_object]
      apply (triangulatedKZeroMap X).range.neg_mem
      exact ⟨TriangulatedK0.mk (SSet.HomotopyCategory.mk
        ((sOneComparison X.carrier).app _ d)), triangulatedKZeroMap_vertex X _⟩
  · intro x y f hf
    rw [singletonCategoryHom_inv, boundaryPathKClass_inv]
    exact (triangulatedKZeroMap X).range.neg_mem hf
  · intro x y z f g hf hg
    rw [singletonCategoryHom_comp, boundaryPathKClass_comp]
    exact (triangulatedKZeroMap X).range.add_mem hf hg

/-- 実際の零次 K 群は元の対象 K 類で生成され、三角圏 K₀ 比較は全射となる。 -/
lemma triangulatedKZeroMap_surjective (X : StableModel.{u}) :
    Function.Surjective (triangulatedKZeroMap X) := by
  intro a
  have h := boundaryPathKClass_mem_triangulatedKZeroRange X (kZeroGroupoidPresentation X a.toMul)
  rw [singletonCategoryHom_self, boundaryPathKClass_presentation] at h
  exact h

end SerrePositivity.KST.SConstruction
