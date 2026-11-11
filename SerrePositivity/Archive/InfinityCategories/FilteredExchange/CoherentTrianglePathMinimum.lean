module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTrianglePathClassification
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.CoherentPathMinimum

/-!
概要：二単体の実 path の最初の正頂点と、その反転の値を計算する。
方針：所属・最小性と実 path の台の式を使う。
規約：非計算的な最小元の選択を変更せず、その値を証明する。
使われ方：元の終点円柱と標準の反転 Hom 比較の全次数での照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 最初の隣接 path の最初の正頂点は 1（零を除いた添字は 0）。 -/
lemma coherentTrianglePath01_firstMinimum :
    pathFirstMinimum (j := (0 : Fin 2)) coherentTrianglePath01.{u} = 0 := by
  have h := pathFirstMinimum_le_end (j := (0 : Fin 2)) coherentTrianglePath01.{u}
  apply Fin.ext
  change (pathFirstMinimum (j := (0 : Fin 2)) coherentTrianglePath01).val ≤ 0 at h
  change _ = (0 : ℕ)
  omega

/-- 元の長辺の最初の正頂点は 2（零を除いた添字は 1）。 -/
lemma coherentTrianglePath02_firstMinimum :
    pathFirstMinimum (j := (1 : Fin 2)) coherentTrianglePath02.{u} = 1 := by
  have h := pathFirstMinimum_mem (j := (1 : Fin 2)) coherentTrianglePath02.{u}
  rw [coherentTrianglePath02_set] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  apply Fin.ext
  rcases h with h | h
  · have hz := congrArg (fun z : ULift.{u} (Fin 3) ↦ z.down.val) h
    change (pathFirstMinimum (j := (1 : Fin 2)) coherentTrianglePath02).val + 1 = 0 at hz
    omega
  · exact Nat.add_right_cancel (show
      (pathFirstMinimum (j := (1 : Fin 2)) coherentTrianglePath02).val + 1 = 1 + 1 from
        congrArg (fun z : ULift.{u} (Fin 3) ↦ z.down.val) h)

/-- 二辺合成 path の最初の正頂点は 1（零を除いた添字は 0）。 -/
lemma coherentTriangleCompositePath_firstMinimum :
    pathFirstMinimum (j := (1 : Fin 2)) coherentTriangleCompositePath.{u} = 0 := by
  have hm : ULift.up (1 : Fin 3) ∈ coherentTriangleCompositePath.{u}.I := by
    rw [coherentTriangleCompositePath_set]
    simp
  have h := pathFirstMinimum_le (j := (1 : Fin 2)) coherentTriangleCompositePath (0 : Fin 2) hm
  apply Fin.ext
  change (pathFirstMinimum (j := (1 : Fin 2)) coherentTriangleCompositePath).val ≤ 0 at h
  change _ = (0 : ℕ)
  omega

/-- 長辺の反転最小点の関手は元の精密化の始点 0 を回収する。 -/
lemma coherentTrianglePath02_reverseMinimum :
    (pathFirstMinimumReverseFunctor.{u} (1 : Fin 2)).obj coherentTrianglePath02 = ULift.up 0 := by
  apply ULift.ext
  apply Fin.ext
  simp [pathFirstMinimumReverseFunctor, pathFirstMinimumIndex, coherentTrianglePath02_firstMinimum]

/-- 合成 path の反転最小点の関手は元の精密化の終点 1 を回収する。 -/
lemma coherentTriangleCompositePath_reverseMinimum :
    (pathFirstMinimumReverseFunctor.{u} (1 : Fin 2)).obj coherentTriangleCompositePath =
      ULift.up 1 := by
  apply ULift.ext
  apply Fin.ext
  simp [pathFirstMinimumReverseFunctor, pathFirstMinimumIndex,
    coherentTriangleCompositePath_firstMinimum]

end SerrePositivity.InfinityCategories.F2
