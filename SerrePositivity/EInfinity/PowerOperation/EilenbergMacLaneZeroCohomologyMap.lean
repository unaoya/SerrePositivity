module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLoopComponents
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneOmegaZeroReduction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyDegreeZero

/-!
# 指定随伴構造射が H⁰ に誘導する自然な写像

DAG XIII §2.2 の零次数の Ω 比較への前段。二つの指定された π/H 比較で共役し、
元の構造射と連結成分の全単射性を同値に保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.KST.Spectra (pointedHomotopyMap pointedHomotopyMap_comp)
variable (A : Type u) [CommRing A]

/-- 基点付き零次ホモトピー類も、同じ Γ の成分比較で H⁰ に戻す。 -/
def gammaBasedPiZeroCohomologyEquiv (M : Complex A) :
    KanHomotopy ((gammaPointedFunctor A).obj M).right 0
      ((gammaPointedFunctor A).obj M).basepoint ≃ M.homology 0 :=
  KanHomotopyZero.equivPiZero.trans (gammaPiZeroCohomologyEquiv A M)

lemma gammaBasedPiZeroCohomologyEquiv_naturality {M N : Complex A} (f : M ⟶ N)
    (a : KanHomotopy ((gammaPointedFunctor A).obj M).right 0
      ((gammaPointedFunctor A).obj M).basepoint) :
    gammaBasedPiZeroCohomologyEquiv A N
      (pointedHomotopyMap 0 ((gammaPointedFunctor A).map f) a) =
      (homologyMap f 0).hom (gammaBasedPiZeroCohomologyEquiv A M a) := by
  change gammaPiZeroCohomologyEquiv A N
    (KanHomotopyZero.equivPiZero (KanHomotopyZero.map
      ((gammaPointedFunctor A).map f).right _ a)) = _
  rw [KanHomotopyZero.equivPiZero_map]
  exact gammaPiZeroCohomologyEquiv_naturality A f _

/-- 指定構造射が同じ二つの π/H 比較を通して誘導する H⁰ 上の写像。 -/
def gammaSuspensionH0Map (M : Complex A) : M.homology 0 → M.homology 0 :=
  gammaLoopPiZeroCohomologyEquiv A M ∘
    pointedHomotopyMap 0 ((gammaAdjointSuspension A).app M) ∘
      (gammaBasedPiZeroCohomologyEquiv A M).symm

lemma gammaSuspensionH0Map_naturality {M N : Complex A} (f : M ⟶ N)
    (x : M.homology 0) :
    gammaSuspensionH0Map A N ((homologyMap f 0).hom x) =
      (homologyMap f 0).hom (gammaSuspensionH0Map A M x) := by
  let b := (gammaBasedPiZeroCohomologyEquiv A M).symm x
  have hb : (gammaBasedPiZeroCohomologyEquiv A N).symm ((homologyMap f 0).hom x) =
      pointedHomotopyMap 0 ((gammaPointedFunctor A).map f) b := by
    apply (gammaBasedPiZeroCohomologyEquiv A N).injective
    rw [Equiv.apply_symm_apply, gammaBasedPiZeroCohomologyEquiv_naturality]
    simp only [b, Equiv.apply_symm_apply]
  have hn : pointedHomotopyMap 0 ((gammaAdjointSuspension A).app N)
      (pointedHomotopyMap 0 ((gammaPointedFunctor A).map f) b) =
      pointedHomotopyMap 0 ((gammaLoopFunctor A).map f)
        (pointedHomotopyMap 0 ((gammaAdjointSuspension A).app M) b) := by
    rw [← pointedHomotopyMap_comp, ← pointedHomotopyMap_comp]
    exact congrArg (fun k => pointedHomotopyMap 0 k b)
      ((gammaAdjointSuspension A).naturality f)
  dsimp only [gammaSuspensionH0Map, Function.comp_apply]
  rw [hb, hn]
  exact gammaLoopPiZeroCohomologyEquiv_naturality A f _

lemma gammaSuspensionH0Map_bijective_iff (M : Complex A) :
    Function.Bijective (gammaSuspensionH0Map A M) ↔
      Function.Bijective (pointedHomotopyMap 0 ((gammaAdjointSuspension A).app M)) :=
  ((gammaLoopPiZeroCohomologyEquiv A M).comp_bijective _).trans
    ((gammaBasedPiZeroCohomologyEquiv A M).symm.bijective_comp _)

end SerrePositivity.EInfinity.PowerOperation
