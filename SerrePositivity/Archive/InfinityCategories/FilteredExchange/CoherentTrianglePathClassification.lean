module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePathSets

/-!
概要：二単体の path は隣接辺では一意、長辺では中間頂点の有無で二種類。
方針：全ての点を端点の間に挟み、三つの頂点で台を比較する。
規約：集合の等式だけでなく元の実 path の等式を保持する。
使われ方：零面の実終点三角形と標準の左 Hom 比較の全 Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 最初の隣接二頂点間の path は元の標準 path。 -/
lemma coherentTrianglePath01_unique
    (P : Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 1)) :
    P = coherentTrianglePath01 := by
  apply SimplicialThickening.Path.ext
  rw [coherentTrianglePath01_set]
  ext k
  rcases k with ⟨k⟩
  fin_cases k
  · exact iff_of_true P.left (by simp)
  · exact iff_of_true P.right (by simp)
  · have hn : ULift.up (2 : Fin 3) ∉ P.I := by
      intro hk
      have h := P.le_right _ hk
      change (2 : Fin 3) ≤ 1 at h
      exact (by decide : ¬ (2 : Fin 3) ≤ 1) h
    exact iff_of_false hn (by decide)

/-- 後半の隣接二頂点間の path は元の標準 path。 -/
lemma coherentTrianglePath12_unique
    (P : Path (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) :
    P = coherentTrianglePath12 := by
  apply SimplicialThickening.Path.ext
  rw [coherentTrianglePath12_set]
  ext k
  rcases k with ⟨k⟩
  fin_cases k
  · have hn : ULift.up (0 : Fin 3) ∉ P.I := by
      intro hk
      have h := P.left_le _ hk
      change (1 : Fin 3) ≤ 0 at h
      exact (by decide : ¬ (1 : Fin 3) ≤ 0) h
    exact iff_of_false hn (by decide)
  · exact iff_of_true P.left (by simp)
  · exact iff_of_true P.right (by simp)

/-- 長辺の実 path は、中間頂点の有無に応じて標準長辺または合成 path。 -/
lemma coherentTrianglePath02_cases
    (P : Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) :
    P = coherentTrianglePath02 ∨ P = coherentTriangleCompositePath := by
  by_cases h : ULift.up (1 : Fin 3) ∈ P.I
  · right
    apply SimplicialThickening.Path.ext
    rw [coherentTriangleCompositePath_set]
    ext k
    rcases k with ⟨k⟩
    fin_cases k
    · exact iff_of_true P.left (by simp)
    · exact iff_of_true h (by simp)
    · exact iff_of_true P.right (by simp)
  · left
    apply SimplicialThickening.Path.ext
    rw [coherentTrianglePath02_set]
    ext k
    rcases k with ⟨k⟩
    fin_cases k
    · exact iff_of_true P.left (by simp)
    · exact iff_of_false h (by decide)
    · exact iff_of_true P.right (by simp)

end SerrePositivity.InfinityCategories.F2
