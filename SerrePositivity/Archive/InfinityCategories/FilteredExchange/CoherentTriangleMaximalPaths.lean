module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MaximalPathFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePaths

/-!
概要：三頂点の最大 path を、元の第一辺・最後辺・二辺合成の path に同定する。
方針：隣接頂点の間に他の頂点がなく、全三頂点は同じ二辺合成に含まれることを使う。
規約：元の指定 path を保持する。
使われ方：最大化した三角形の strict な三射の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SimplicialThickening
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：最初の隣接区間の最大 path を回収。方針：端点と三頂点の判定。
規約：元の第一辺を保持。使われ方：最大化の最初の射の正規化。 -/
lemma coherentTriangleMaximalPath01 :
    coherentMaximalPath
      (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1 by decide) =
        coherentTrianglePath01 := by
  apply SimplicialThickening.Path.ext
  apply Set.Subset.antisymm
  · intro k hk
    rcases k with ⟨k⟩
    have hk' : k ≤ (1 : Fin 3) := hk.2
    fin_cases k
    · exact coherentTrianglePath01.left
    · exact coherentTrianglePath01.right
    · simp at hk'
  · intro k hk
    exact ⟨coherentTrianglePath01.left_le k hk, coherentTrianglePath01.le_right k hk⟩

/-- 概要：最後の隣接区間の最大 path を回収。方針：端点と三頂点の判定。
規約：元の最後辺を保持。使われ方：最大化の最後の射の正規化。 -/
lemma coherentTriangleMaximalPath12 :
    coherentMaximalPath
      (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 by decide) =
        coherentTrianglePath12 := by
  apply SimplicialThickening.Path.ext
  apply Set.Subset.antisymm
  · intro k hk
    rcases k with ⟨k⟩
    have hk' : (1 : Fin 3) ≤ k := hk.1
    fin_cases k
    · simp at hk'
    · exact coherentTrianglePath12.left
    · exact coherentTrianglePath12.right
  · intro k hk
    exact ⟨coherentTrianglePath12.left_le k hk, coherentTrianglePath12.le_right k hk⟩

/-- 概要：最大の長区間は元の二辺合成。方針：同じ全三頂点の台を照合。
規約：指定合成 path を保持。使われ方：最大化の長射を二射の合成へ戻す。 -/
lemma coherentTriangleMaximalPath02 :
    coherentMaximalPath
      (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 by decide) =
        coherentTriangleCompositePath := by
  apply SimplicialThickening.Path.ext
  apply Set.Subset.antisymm
  · rintro ⟨k⟩ hk
    change ULift.up k ∈ coherentTrianglePath01.I ∪ coherentTrianglePath12.I
    fin_cases k
    · exact Or.inl coherentTrianglePath01.left
    · exact Or.inl coherentTrianglePath01.right
    · exact Or.inr coherentTrianglePath12.right
  · intro k hk
    exact ⟨coherentTriangleCompositePath.left_le k hk, coherentTriangleCompositePath.le_right k hk⟩

end SerrePositivity.InfinityCategories.F2
