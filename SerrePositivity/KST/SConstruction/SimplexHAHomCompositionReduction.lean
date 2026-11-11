module
public import SerrePositivity.KST.SConstruction.SimplexHAHomEasyComposition

/-! # 元の全 HA Hom 合成の厳密三頂点の場合への帰着
概要：元の全三頂点の合成保存は、厳密昇順の三頂点での合成保存から従う。
方針：元の有限頂点順序で場合分けし、実対角合成と実零 Hom の場合を既存式で閉じる。
規約：厳密昇順の場合の入力を明記。使われ方：元の interval composition との主比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の厳密三頂点で合成を保てば、対角と逆向きも含む元の全三頂点で合成を保つ。 -/
lemma simplexHAHomMap_comp_of_strict {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (hstrict : ∀ (a b c : Fin (N + 1)), a < b → b < c →
      eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
          simplexHAHomMap A s a c =
        (simplexHAHomMap A s a b ⊗ₘ simplexHAHomMap A s b c) ≫
          eComp (Complex A) (s.obj a) (s.obj b) (s.obj c)) (a b c : Fin (N + 1)) :
    eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
        simplexHAHomMap A s a c =
      (simplexHAHomMap A s a b ⊗ₘ simplexHAHomMap A s b c) ≫
        eComp (Complex A) (s.obj a) (s.obj b) (s.obj c) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rcases lt_trichotomy b c with hbc | rfl | hcb
    · exact hstrict a b c hab hbc
    · exact simplexHAHomMap_comp_right_diagonal A s a b
    · exact simplexHAHomMap_comp_right_reverse A s a b c hcb
  · exact simplexHAHomMap_comp_left_diagonal A s a c
  · exact simplexHAHomMap_comp_left_reverse A s a b c hba

end SerrePositivity.KST.SConstruction
