module

public import SerrePositivity.InfinityCategories.F2.CoherentCompositionTetrahedron

/-!
概要：比較三単体の最大 path を元の対象写像で送ると同じ全区間を回収する。
方針：元の時刻付き変形の support を有限の区間として計算する。
規約：任意の Hom の path とその端点を保持する。
使われ方：固定始点の coslice 円柱の最大化側を元の標準族へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 比較三単体の最大 path の像は元の二端点間の最大 path。 -/
lemma coherentCompositionTetrahedron_maximal_path
    {i j : ULift.{u} (Fin 4)} (P : Path i j) :
    coherentPathDeformation coherentCompositionTetrahedronObjects
      coherentCompositionTetrahedronTime
        (coherentPathDeformation OrderHom.id (OrderHom.const _ 1) P) =
    coherentPathDeformation OrderHom.id (OrderHom.const _ 1)
      ((SimplicialThickening.functorMap coherentCompositionTetrahedronObjects
        ⟨i⟩ ⟨j⟩).obj P) := by
  apply SimplicialThickening.Path.ext
  change coherentCompositionTetrahedronObjects ''
      (coherentPathDeformation OrderHom.id (OrderHom.const _ 1) P).I ∪
      {z | ∃ k ∈ (coherentPathDeformation OrderHom.id (OrderHom.const _ 1) P).I,
        coherentCompositionTetrahedronTime k = 1 ∧
          coherentCompositionTetrahedronObjects k ≤ z ∧
            z ≤ coherentCompositionTetrahedronObjects j} = _
  rw [coherentPathDeformation_one, coherentPathDeformation_one]
  have hij := P.le
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j <;> try (exfalso; simpa using hij)
  all_goals
    ext z
    rcases z with ⟨z⟩
    fin_cases z <;>
      simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_Icc,
        ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;> decide

end SerrePositivity.InfinityCategories.F2
