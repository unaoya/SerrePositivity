module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ResolutionPath

/-!
# 解像の旗の引き戻しと Path の末尾への制限

概要：解像の正規化した引き戻しは、選んだ最初の最大頂点からの Path の末尾に等しい。
方針：切断点の所属を単調性で示し、最後以外の各頂点で filter の所属を比較する。
規約：新しい始点は最初に選んだ段の最大元であり、元の始点とは限らない。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の解像上の Hom 写像の自然性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening

/-- 概要：引き戻しの新しい始点は、選んだ後の全ての Path に属する。
方針：最初に選んだ段の最大元の所属を旗の単調性で後の段へ写す。
規約：切断点を元の頂点番号から持ち上げて表す。
使われ方：Kerodon 2.5.9（Tag 00SC） の各 Path の前半と後半への分解。 -/
lemma resolutionFlagPath_cut_mem {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (t : Fin (e + 1)) :
    ULift.up (F.maxAt (α 0)).castSucc ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath.{u} F (α t)).I := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_resolutionFlagPath_iff F (α t) _).mpr
  exact F.monotone_sets (α.monotone (Fin.zero_le t)) (F.maxAt_mem (α 0))

/-- 概要：解像の引き戻しの Path は、選んだ元の Path の新しい始点からの末尾に等しい。
方針：最後の頂点と castSucc の頂点に分け、後者で有限集合の filter の条件を使う。
規約：単体の添字の写像は退化を含む任意の単調写像。
使われ方：HA 1.3.1.17 の pinched 条件の単位保存を使った面・退化との可換性。 -/
lemma resolutionFlagPath_pullback {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (t : Fin (e + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathSuffix (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath.{u} F (α t))
      (ULift.up (F.maxAt (α 0)).castSucc) (resolutionFlagPath_cut_mem F α t) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath (F.pullback α) t := by
  apply CategoryTheory.SimplicialThickening.Path.ext
  apply Set.ext
  rintro ⟨z⟩
  induction z using Fin.lastCases with
  | last =>
    constructor
    · intro _
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath (F.pullback α) t).right
    · intro _
      exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath F (α t)).right, (Fin.castSucc_lt_last _).le⟩
  | cast j =>
    change (ULift.up j.castSucc ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath F (α t)).I ∧
      (ULift.up (F.maxAt (α 0)).castSucc : ULift.{u} (Fin (n + 2))) ≤ ULift.up j.castSucc) ↔
        ULift.up j.castSucc ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath (F.pullback α) t).I
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_resolutionFlagPath_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_resolutionFlagPath_iff]
    change (j ∈ F.sets (α t) ∧ F.maxAt (α 0) ≤ j) ↔
      j ∈ (F.sets (α t)).filter (fun k ↦ F.maxAt (α 0) ≤ k)
    exact Finset.mem_filter.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
